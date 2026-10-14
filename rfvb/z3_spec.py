"""Z3 semantic equivalence verifier for Lean 4 specifications.

Translates the lowered JSON AST produced by `Benchmark.SpecAudit` into Z3
constraints and checks four semantic facets under the task's preconditions `Pre`:
  1. Soundness:      Pre ∧ CandidateSpec ⇒ OracleSpec   (UNSAT on Pre ∧ Cand ∧ ¬Oracle)
  2. Completeness:   Pre ∧ OracleSpec ⇒ CandidateSpec   (UNSAT on Pre ∧ Oracle ∧ ¬Cand)
  3. Non-Vacuity:    ∃ vars, Pre ∧ CandidateSpec        (SAT)
  4. Non-Triviality: ∃ vars, Pre ∧ ¬CandidateSpec       (SAT)
"""
from __future__ import annotations

import json
import threading
from dataclasses import dataclass, field
from typing import Any

import z3

_Z3_LOCK = threading.Lock()

SCALAR_BOUNDS: dict[str, tuple[int | None, int | None, int | None]] = {
    "u8": (0, (1 << 8) - 1, 8),
    "u16": (0, (1 << 16) - 1, 16),
    "u32": (0, (1 << 32) - 1, 32),
    "u64": (0, (1 << 64) - 1, 64),
    "usize": (0, (1 << 64) - 1, 64),
    "u128": (0, (1 << 128) - 1, 128),
    "i8": (-(1 << 7), (1 << 7) - 1, 8),
    "i16": (-(1 << 15), (1 << 15) - 1, 16),
    "i32": (-(1 << 31), (1 << 31) - 1, 32),
    "i64": (-(1 << 63), (1 << 63) - 1, 64),
    "isize": (-(1 << 63), (1 << 63) - 1, 64),
    "i128": (-(1 << 127), (1 << 127) - 1, 128),
    "nat": (0, None, None),
    "ordering": (-1, 1, None),
    "int": (None, None, None),
}


@dataclass
class Z3AuditResult:
    passed: bool
    status: str  # passed | unsound_spec | incomplete_spec | vacuous_spec | trivial_spec | solver_unknown
    soundness: str = ""
    completeness: str = ""
    nonvacuity: str = ""
    nontriviality: str = ""
    counterexample: dict[str, str] | None = None
    detail: str = ""

    def to_json(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "status": self.status,
            "soundness": self.soundness,
            "completeness": self.completeness,
            "nonvacuity": self.nonvacuity,
            "nontriviality": self.nontriviality,
            "counterexample": self.counterexample,
            "detail": self.detail,
        }


def _subst_var_ast(node: Any, vname: str, val_int: int) -> Any:
    if isinstance(node, dict):
        if node.get("var") == vname:
            return {"int": val_int}
        return {k: _subst_var_ast(v, vname, val_int) for k, v in node.items()}
    if isinstance(node, list):
        return [_subst_var_ast(x, vname, val_int) for x in node]
    return node


def _mentions_var(node: Any, vname: str) -> bool:
    if isinstance(node, dict):
        if node.get("var") == vname:
            return True
        return any(_mentions_var(v, vname) for v in node.values())
    if isinstance(node, list):
        return any(_mentions_var(x, vname) for x in node)
    return False


def _subst_var_node(node: Any, vname: str, repl: Any) -> Any:
    if isinstance(node, dict):
        if node.get("var") == vname:
            return repl
        return {k: _subst_var_node(v, vname, repl) for k, v in node.items()}
    if isinstance(node, list):
        return [_subst_var_node(x, vname, repl) for x in node]
    return node


def _extract_eq_witness(vname: str, cond: Any) -> tuple[Any, list[Any]] | None:
    if not isinstance(cond, dict):
        return None
    op = cond.get("op")
    cargs = cond.get("args", [])
    if op == "eq" and len(cargs) == 2:
        lhs, rhs = cargs[0], cargs[1]
        if isinstance(lhs, dict) and lhs.get("var") == vname and not _mentions_var(rhs, vname):
            return rhs, []
        if isinstance(rhs, dict) and rhs.get("var") == vname and not _mentions_var(lhs, vname):
            return lhs, []
    if op == "and" and len(cargs) == 2:
        w0 = _extract_eq_witness(vname, cargs[0])
        if w0 is not None:
            return w0[0], w0[1] + [cargs[1]]
        w1 = _extract_eq_witness(vname, cargs[1])
        if w1 is not None:
            return w1[0], [cargs[0]] + w1[1]
    return None


def _extract_one_point_forall(vname: str, body: Any) -> tuple[Any, Any] | None:
    if not isinstance(body, dict) or body.get("op") != "implies":
        return None
    args = body.get("args", [])
    if len(args) != 2:
        return None
    cond, rest = args[0], args[1]
    w = _extract_eq_witness(vname, cond)
    if w is None:
        return None
    rhs, rem_conds = w
    new_rest = rest
    for rc in reversed(rem_conds):
        new_rest = {"op": "implies", "args": [rc, new_rest]}
    return rhs, _subst_var_node(new_rest, vname, rhs)


def _extract_one_point_exists(vname: str, body: Any) -> tuple[Any, Any] | None:
    w = _extract_eq_witness(vname, body)
    if w is None:
        return None
    rhs, rem_conds = w
    if not rem_conds:
        new_rest: Any = {"op": "true", "args": []}
    else:
        new_rest = rem_conds[0]
        for rc in rem_conds[1:]:
            new_rest = {"op": "and", "args": [new_rest, rc]}
    return rhs, _subst_var_node(new_rest, vname, rhs)


def _extract_small_bounds(vname: str, sort: str, body: Any) -> tuple[int, int, Any] | None:
    if not isinstance(body, dict) or body.get("op") != "implies":
        return None
    args = body.get("args", [])
    if len(args) != 2:
        return None
    cond, rest = args[0], args[1]
    lo: int | None = 0 if sort in ("nat", "u8", "u16", "u32", "u64", "usize", "u128") else None
    hi: int | None = None

    def parse_bound(c: Any) -> bool:
        nonlocal lo, hi
        if not isinstance(c, dict):
            return False
        op = c.get("op")
        cargs = c.get("args", [])
        if op == "lt" and len(cargs) == 2 and cargs[0].get("var") == vname and "int" in cargs[1]:
            hi = int(cargs[1]["int"])
            return True
        if op == "le" and len(cargs) == 2 and cargs[0].get("var") == vname and "int" in cargs[1]:
            hi = int(cargs[1]["int"]) + 1
            return True
        if op == "le" and len(cargs) == 2 and "int" in cargs[0] and cargs[1].get("var") == vname:
            lo = int(cargs[0]["int"])
            return True
        if op == "lt" and len(cargs) == 2 and "int" in cargs[0] and cargs[1].get("var") == vname:
            lo = int(cargs[0]["int"]) + 1
            return True
        if op == "and" and len(cargs) == 2:
            return parse_bound(cargs[0]) and parse_bound(cargs[1])
        return False

    if parse_bound(cond) and lo is not None and hi is not None and 0 <= hi - lo <= 16:
        return lo, hi, rest
    return None


def _collect_free_vars(node: Any, bound_set: set[str], out_list: list[tuple[str, str]]) -> None:
    if isinstance(node, dict):
        if "var" in node:
            vn = str(node["var"])
            sort = str(node.get("sort", "int"))
            if not vn.startswith("_lam_") and vn not in bound_set:
                if (vn, sort) not in out_list:
                    out_list.append((vn, sort))
            return
        if node.get("op") in ("forall", "exists"):
            new_bound = bound_set | {str(v["name"]) for v in node.get("vars", [])}
            _collect_free_vars(node.get("body"), new_bound, out_list)
            return
        for v in node.values():
            _collect_free_vars(v, bound_set, out_list)
    elif isinstance(node, list):
        for x in node:
            _collect_free_vars(x, bound_set, out_list)


def _replace_free_vars(node: Any, fmap: dict[str, str]) -> Any:
    if isinstance(node, dict):
        if "var" in node and node["var"] in fmap:
            return {"var": fmap[node["var"]], "sort": node.get("sort", "int")}
        return {k: _replace_free_vars(v, fmap) for k, v in node.items()}
    if isinstance(node, list):
        return [_replace_free_vars(x, fmap) for x in node]
    return node


def _to_bool(e: z3.ExprRef) -> z3.BoolRef:
    if z3.is_bool(e):
        return e
    return e != z3.IntVal(0)


def _to_int(e: z3.ExprRef) -> z3.ArithRef:
    if z3.is_int(e):
        return e
    if z3.is_bool(e):
        return z3.If(e, z3.IntVal(1), z3.IntVal(0))
    return e


def _sort_bounds_expr(var_ref: z3.ExprRef, sort: str) -> list[z3.BoolRef]:
    if sort == "bool" or not z3.is_int(var_ref):
        return []
    lo, hi, _ = SCALAR_BOUNDS.get(sort, (None, None, None))
    out: list[z3.BoolRef] = []
    if lo is not None:
        out.append(var_ref >= z3.IntVal(lo))
    if hi is not None:
        out.append(var_ref <= z3.IntVal(hi))
    return out


class ASTTranslator:
    def __init__(self, vars_info: list[dict[str, str]]) -> None:
        self.var_sorts: dict[str, str] = {}
        self.vars: dict[str, z3.ExprRef] = {}
        self.ufs: dict[tuple[Any, ...], z3.FuncDeclRef] = {}
        self.uf_constraints: dict[str, z3.BoolRef] = {}
        self.bound_depth: int = 0
        for v in vars_info:
            name = v["name"]
            sort = v.get("sort", "int")
            self.var_sorts[name] = sort
            self.vars[name] = z3.Bool(name) if sort == "bool" else z3.Int(name)

    def get_var(self, name: str, sort: str) -> z3.ExprRef:
        if name not in self.vars:
            self.var_sorts[name] = sort
            self.vars[name] = z3.Bool(name) if sort == "bool" else z3.Int(name)
        return self.vars[name]

    def var_bounds(self) -> list[z3.BoolRef]:
        out: list[z3.BoolRef] = []
        for name, vref in self.vars.items():
            if name.startswith(("_q_", "_ex_", "_lam_")):
                continue
            sort = self.var_sorts.get(name, "int")
            out.extend(_sort_bounds_expr(vref, sort))
        return out

    def _apply_uf(self, kind: str, fn: str, leaf: int, ret_sort_name: str, args: list[z3.ExprRef]) -> z3.ExprRef:
        coerced_args: list[z3.ExprRef] = []
        arg_sorts: list[z3.SortRef] = []
        for a in args:
            if z3.is_bool(a):
                coerced_args.append(a)
                arg_sorts.append(z3.BoolSort())
            else:
                ia = _to_int(a)
                coerced_args.append(ia)
                arg_sorts.append(z3.IntSort())
        ret_sort = z3.BoolSort() if ret_sort_name == "bool" else z3.IntSort()
        key = (kind, fn, leaf, tuple(str(s) for s in arg_sorts), str(ret_sort))
        if key not in self.ufs:
            uf_name = f"{kind}:{fn}:{leaf}:{len(self.ufs)}"
            self.ufs[key] = z3.Function(uf_name, *arg_sorts, ret_sort)
        decl = self.ufs[key]
        app = decl(*coerced_args) if coerced_args else decl()
        if self.bound_depth == 0 and ret_sort_name != "bool":
            for b in _sort_bounds_expr(app, ret_sort_name):
                self.uf_constraints[str(b)] = b
        return app

    def translate(self, node: Any) -> z3.ExprRef:
        if isinstance(node, dict):
            if "int" in node:
                return z3.IntVal(int(node["int"]))
            if "var" in node:
                return self.get_var(str(node["var"]), str(node.get("sort", "int")))
            op = node.get("op")
            if op == "true":
                return z3.BoolVal(True)
            if op == "false":
                return z3.BoolVal(False)
            if op == "lam":
                body = node.get("body")
                free_vars: list[tuple[str, str]] = []
                _collect_free_vars(body, set(), free_vars)
                fmap = {vn: f"$free_{i}" for i, (vn, _) in enumerate(free_vars)}
                canon_body = json.dumps(_replace_free_vars(body, fmap), sort_keys=True, separators=(",", ":"))
                fargs = [self.get_var(vn, vsort) for vn, vsort in free_vars]
                return self._apply_uf("lam", canon_body, 0, "int", fargs)
            if op in ("forall", "exists"):
                qvars_info = node.get("vars", [])
                body = node.get("body")
                if len(qvars_info) == 1:
                    v0 = qvars_info[0]
                    qname = v0["name"]
                    qsort = v0.get("sort", "int")
                    if op == "forall":
                        one_pt = _extract_one_point_forall(qname, body)
                        if one_pt is not None:
                            rhs_node, rest_node = one_pt
                            rhs_z3 = self.translate(rhs_node)
                            rest_z3 = _to_bool(self.translate(rest_node))
                            bounds_z3 = _sort_bounds_expr(rhs_z3, qsort)
                            return z3.Implies(z3.And(*bounds_z3), rest_z3) if bounds_z3 else rest_z3
                        unrolled = _extract_small_bounds(qname, qsort, body)
                        if unrolled is not None:
                            lo, hi, rest = unrolled
                            if lo == hi:
                                return z3.BoolVal(True)
                            conj = [
                                _to_bool(self.translate(_subst_var_ast(rest, qname, k)))
                                for k in range(lo, hi)
                            ]
                            return z3.And(*conj) if len(conj) > 1 else conj[0]
                    elif op == "exists":
                        one_pt_ex = _extract_one_point_exists(qname, body)
                        if one_pt_ex is not None:
                            rhs_node, rest_node = one_pt_ex
                            rhs_z3 = self.translate(rhs_node)
                            rest_z3 = _to_bool(self.translate(rest_node))
                            bounds_z3 = _sort_bounds_expr(rhs_z3, qsort)
                            return z3.And(*bounds_z3, rest_z3) if bounds_z3 else rest_z3
                z3_qvars: list[z3.ExprRef] = []
                q_bounds: list[z3.BoolRef] = []
                for qv in qvars_info:
                    qname = qv["name"]
                    qsort = qv.get("sort", "int")
                    vref = self.get_var(qname, qsort)
                    z3_qvars.append(vref)
                    q_bounds.extend(_sort_bounds_expr(vref, qsort))
                self.bound_depth += 1
                try:
                    body_z3 = _to_bool(self.translate(body))
                finally:
                    self.bound_depth -= 1
                if not z3_qvars:
                    return body_z3
                if op == "forall":
                    guarded = z3.Implies(z3.And(*q_bounds), body_z3) if q_bounds else body_z3
                    return z3.ForAll(z3_qvars, guarded)
                else:
                    guarded = z3.And(*q_bounds, body_z3) if q_bounds else body_z3
                    return z3.Exists(z3_qvars, guarded)

            args = [self.translate(a) for a in node.get("args", [])]
            if op == "not":
                return z3.Not(_to_bool(args[0]))
            if op == "and":
                return z3.And(_to_bool(args[0]), _to_bool(args[1]))
            if op == "or":
                return z3.Or(_to_bool(args[0]), _to_bool(args[1]))
            if op == "implies":
                return z3.Implies(_to_bool(args[0]), _to_bool(args[1]))
            if op == "iff":
                return _to_bool(args[0]) == _to_bool(args[1])
            if op == "eq":
                if z3.is_bool(args[0]) or z3.is_bool(args[1]):
                    return _to_bool(args[0]) == _to_bool(args[1])
                return _to_int(args[0]) == _to_int(args[1])
            if op == "lt":
                return _to_int(args[0]) < _to_int(args[1])
            if op == "le":
                return _to_int(args[0]) <= _to_int(args[1])
            if op == "if":
                cond = _to_bool(args[0])
                t_br, f_br = args[1], args[2]
                if z3.is_bool(t_br) or z3.is_bool(f_br):
                    return z3.If(cond, _to_bool(t_br), _to_bool(f_br))
                return z3.If(cond, _to_int(t_br), _to_int(f_br))
            if op == "add":
                return _to_int(args[0]) + _to_int(args[1])
            if op == "sub":
                return _to_int(args[0]) - _to_int(args[1])
            if op == "natsub":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                return z3.If(a0 >= a1, a0 - a1, z3.IntVal(0))
            if op == "mul":
                return _to_int(args[0]) * _to_int(args[1])
            if op == "neg":
                return -_to_int(args[0])
            if op == "min":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                return z3.If(a0 <= a1, a0, a1)
            if op == "max":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                return z3.If(a0 >= a1, a0, a1)
            if op == "div":
                return _to_int(args[0]) / _to_int(args[1])
            if op == "mod":
                return _to_int(args[0]) % _to_int(args[1])
            if op == "pow":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                if z3.is_int_value(a0) and z3.is_int_value(a1):
                    v0, v1 = a0.as_long(), a1.as_long()
                    if 0 <= v1 <= 256:
                        return z3.IntVal(v0 ** v1)
                if z3.is_int_value(a1):
                    v1 = a1.as_long()
                    if v1 == 0:
                        return z3.IntVal(1)
                    if v1 == 1:
                        return a0
                    if 2 <= v1 <= 8:
                        acc = a0
                        for _ in range(v1 - 1):
                            acc = acc * a0
                        return acc
                if z3.is_int_value(a0):
                    v0 = a0.as_long()
                    if v0 == 1:
                        return z3.IntVal(1)
                    if 2 <= v0 <= 16:
                        acc_pow: z3.ExprRef = self._apply_uf("op", "pow", 0, "int", [a0, a1])
                        exps = [e for e in range(33) if v0 ** e <= (1 << 64)]
                        for e in reversed(exps):
                            acc_pow = z3.If(a1 == z3.IntVal(e), z3.IntVal(v0 ** e), acc_pow)
                        return acc_pow
                return self._apply_uf("op", "pow", 0, "int", [a0, a1])
            if op == "shl":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                if z3.is_int_value(a0) and z3.is_int_value(a1):
                    v0, v1 = a0.as_long(), a1.as_long()
                    if 0 <= v1 <= 256:
                        return z3.IntVal(v0 << v1)
                if z3.is_int_value(a1):
                    v1 = a1.as_long()
                    if 0 <= v1 <= 128:
                        return a0 * z3.IntVal(1 << v1)
                return self._apply_uf("op", "shl", 0, "int", [a0, a1])
            if op == "shr":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                if z3.is_int_value(a0) and z3.is_int_value(a1):
                    v0, v1 = a0.as_long(), a1.as_long()
                    if 0 <= v1 <= 256:
                        return z3.IntVal(v0 >> v1)
                if z3.is_int_value(a1):
                    v1 = a1.as_long()
                    if 0 <= v1 <= 128:
                        return a0 / z3.IntVal(1 << v1)
                return self._apply_uf("op", "shr", 0, "int", [a0, a1])
            if op == "bitand":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                if z3.is_int_value(a0) and z3.is_int_value(a1):
                    return z3.IntVal(a0.as_long() & a1.as_long())
                if z3.is_int_value(a1):
                    m = a1.as_long()
                    if m == 0:
                        return z3.IntVal(0)
                    if m > 0 and (m & (m + 1)) == 0:
                        return z3.If(a0 >= 0, a0 % z3.IntVal(m + 1), self._apply_uf("op", "bitand", 0, "int", [a0, a1]))
                if z3.is_int_value(a0):
                    m = a0.as_long()
                    if m == 0:
                        return z3.IntVal(0)
                    if m > 0 and (m & (m + 1)) == 0:
                        return z3.If(a1 >= 0, a1 % z3.IntVal(m + 1), self._apply_uf("op", "bitand", 0, "int", [a0, a1]))
                return self._apply_uf("op", "bitand", 0, "int", [a0, a1])
            if op == "bitor":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                if z3.is_int_value(a0) and z3.is_int_value(a1):
                    return z3.IntVal(a0.as_long() | a1.as_long())
                if z3.is_int_value(a1) and a1.as_long() == 0:
                    return a0
                if z3.is_int_value(a0) and a0.as_long() == 0:
                    return a1
                return self._apply_uf("op", "bitor", 0, "int", [a0, a1])
            if op == "bitxor":
                a0, a1 = _to_int(args[0]), _to_int(args[1])
                if z3.is_int_value(a0) and z3.is_int_value(a1):
                    return z3.IntVal(a0.as_long() ^ a1.as_long())
                if z3.is_int_value(a1) and a1.as_long() == 0:
                    return a0
                if z3.is_int_value(a0) and a0.as_long() == 0:
                    return a1
                return self._apply_uf("op", "bitxor", 0, "int", [a0, a1])
            if op in ("call_ok", "call_val", "call_err", "uf_prop", "uf_term"):
                fn = str(node.get("fn", ""))
                leaf = int(node.get("leaf", 0))
                sort = str(node.get("sort", "bool" if op in ("call_ok", "uf_prop") else "int"))
                return self._apply_uf(op, fn, leaf, sort, args)
        raise ValueError(f"Unsupported AST node: {node}")


def _purify_nonlinear(expr: z3.ExprRef, memo: dict[int, z3.ExprRef], ufs: dict[str, z3.FuncDeclRef]) -> z3.ExprRef:
    eid = expr.get_id()
    if eid in memo:
        return memo[eid]
    if z3.is_quantifier(expr):
        # Rebuild quantifier with purified body
        qvars = [z3.Const(expr.var_name(i), expr.var_sort(i)) for i in range(expr.num_vars())]
        # Substitute de-Bruijn vars with fresh consts, purify, and re-quantify
        inst_body = z3.substitute_vars(expr.body(), *reversed(qvars))
        p_body = _purify_nonlinear(inst_body, memo, ufs)
        res = z3.ForAll(qvars, p_body) if expr.is_forall() else z3.Exists(qvars, p_body)
        memo[eid] = res
        return res
    num = expr.num_args()
    if num == 0:
        memo[eid] = expr
        return expr
    ch = [_purify_nonlinear(expr.arg(i), memo, ufs) for i in range(num)]
    k = expr.decl().kind()
    if k in (z3.Z3_OP_DIV, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_MUL):
        # Only purify if nonlinear (neither operand is a concrete integer constant)
        if not (z3.is_int_value(ch[0]) or z3.is_int_value(ch[1])):
            op_name = {z3.Z3_OP_DIV: "div", z3.Z3_OP_IDIV: "idiv", z3.Z3_OP_MOD: "mod", z3.Z3_OP_MUL: "mul"}[k]
            if op_name not in ufs:
                ufs[op_name] = z3.Function(f"_nl_{op_name}", z3.IntSort(), z3.IntSort(), z3.IntSort())
            res = ufs[op_name](_to_int(ch[0]), _to_int(ch[1]))
            memo[eid] = res
            return res
    res = expr.decl()(*ch)
    memo[eid] = res
    return res


def _bound_forall_domain(expr: z3.ExprRef, memo: dict[int, z3.ExprRef], max_val: int = 3) -> z3.ExprRef:
    eid = expr.get_id()
    if eid in memo:
        return memo[eid]
    if z3.is_quantifier(expr):
        qvars = [z3.Const(expr.var_name(i), expr.var_sort(i)) for i in range(expr.num_vars())]
        inst_body = z3.substitute_vars(expr.body(), *reversed(qvars))
        b_body = _bound_forall_domain(inst_body, memo, max_val)
        if expr.is_forall():
            int_bounds = [z3.And(q >= 0, q < max_val) for q in qvars if q.sort() == z3.IntSort()]
            if int_bounds:
                b_body = z3.Implies(z3.And(*int_bounds), b_body)
            res = z3.ForAll(qvars, b_body)
        else:
            res = z3.Exists(qvars, b_body)
        memo[eid] = res
        return res
    num = expr.num_args()
    if num == 0:
        memo[eid] = expr
        return expr
    ch = [_bound_forall_domain(expr.arg(i), memo, max_val) for i in range(num)]
    res = expr.decl()(*ch)
    memo[eid] = res
    return res


def _check_formula(formula: z3.BoolRef, timeout_ms: int = 10000) -> tuple[z3.CheckSatResult, z3.Solver]:
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(formula)
    r = s.check()
    if r == z3.unknown:
        s2 = z3.Solver()
        s2.set("timeout", timeout_ms)
        memo: dict[int, z3.ExprRef] = {}
        nl_ufs: dict[str, z3.FuncDeclRef] = {}
        purified = _to_bool(_purify_nonlinear(formula, memo, nl_ufs))
        s2.add(purified)
        r2 = s2.check()
        if r2 != z3.unknown:
            return r2, s2
        s3 = z3.Solver()
        s3.set("timeout", timeout_ms)
        s3.add(_to_bool(_bound_forall_domain(purified, {})))
        r3 = s3.check()
        if r3 != z3.unknown:
            return r3, s3
    return r, s


def _extract_model(solver: z3.Solver, vars_dict: dict[str, z3.ExprRef]) -> dict[str, str]:
    out: dict[str, str] = {}
    try:
        m = solver.model()
        for name, vref in vars_dict.items():
            if name.startswith(("_q_", "_ex_", "_lam_")):
                continue
            val = m.eval(vref, model_completion=True)
            out[name] = str(val)
    except Exception:
        pass
    return out


def check_spec_equivalence(audit_data: dict[str, Any], timeout_ms: int = 10000) -> Z3AuditResult:
    with _Z3_LOCK:
        return _check_spec_equivalence_locked(audit_data, timeout_ms)


def _check_spec_equivalence_locked(audit_data: dict[str, Any], timeout_ms: int = 10000) -> Z3AuditResult:
    tr = ASTTranslator(audit_data.get("vars", []))
    pre_nodes = audit_data.get("preconditions", [])
    pre_exprs = [_to_bool(tr.translate(p)) for p in pre_nodes]
    oracle_expr = _to_bool(tr.translate(audit_data["oracle"]))
    cand_expr = _to_bool(tr.translate(audit_data["candidate"]))

    all_pre = tr.var_bounds() + list(tr.uf_constraints.values()) + pre_exprs
    pre_conj = z3.And(*all_pre) if all_pre else z3.BoolVal(True)

    # 1. Soundness: Pre ∧ Cand ∧ ¬Oracle (must be UNSAT)
    r_sound, s_sound = _check_formula(z3.And(pre_conj, cand_expr, z3.Not(oracle_expr)), timeout_ms)
    # 2. Completeness: Pre ∧ Oracle ∧ ¬Cand (must be UNSAT)
    r_comp, s_comp = _check_formula(z3.And(pre_conj, oracle_expr, z3.Not(cand_expr)), timeout_ms)
    # 3. Non-vacuity: Pre ∧ Cand (must be SAT)
    r_nonvac, _ = _check_formula(z3.And(pre_conj, cand_expr), timeout_ms)
    # 4. Non-triviality: Pre ∧ ¬Cand (must be SAT)
    r_nontriv, _ = _check_formula(z3.And(pre_conj, z3.Not(cand_expr)), timeout_ms)

    res = Z3AuditResult(
        passed=False,
        status="solver_unknown",
        soundness=str(r_sound),
        completeness=str(r_comp),
        nonvacuity=str(r_nonvac),
        nontriviality=str(r_nontriv),
    )

    if r_nonvac == z3.unsat:
        res.status = "vacuous_spec"
        res.detail = "Candidate specification is contradictory/vacuous under the domain preconditions (Pre ∧ CandidateSpec is UNSAT)."
        return res
    if r_nontriv == z3.unsat:
        res.status = "trivial_spec"
        res.detail = "Candidate specification is a tautology under the domain preconditions (Pre ∧ ¬CandidateSpec is UNSAT)."
        return res
    if r_sound == z3.sat:
        res.status = "unsound_spec"
        res.counterexample = _extract_model(s_sound, tr.vars)
        res.detail = f"Candidate specification does not imply the target property (Pre ∧ CandidateSpec ∧ ¬OracleSpec is SAT). Counterexample: {res.counterexample}"
        return res
    if r_comp == z3.sat:
        res.status = "incomplete_spec"
        res.counterexample = _extract_model(s_comp, tr.vars)
        res.detail = f"Candidate specification is strictly stronger than or incompatible with the target property (Pre ∧ OracleSpec ∧ ¬CandidateSpec is SAT). Counterexample: {res.counterexample}"
        return res
    if r_sound == z3.unsat and r_comp == z3.unsat and r_nonvac == z3.sat and r_nontriv == z3.sat:
        res.passed = True
        res.status = "passed"
        res.detail = "All 4 Z3 equivalence checks passed (soundness=unsat, completeness=unsat, nonvacuity=sat, nontriviality=sat)."
        return res

    res.status = "solver_unknown"
    res.detail = f"Z3 returned unknown on one or more checks (soundness={r_sound}, completeness={r_comp}, nonvacuity={r_nonvac}, nontriviality={r_nontriv})."
    return res
