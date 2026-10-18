import Crc16Presets.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for crc16.ARC
deriving instance Repr for crc16.ARC
deriving instance DecidableEq for crc16.DNP
deriving instance Repr for crc16.DNP
deriving instance DecidableEq for crc16.MAXIM
deriving instance Repr for crc16.MAXIM
deriving instance DecidableEq for crc16.MCRF4XX
deriving instance Repr for crc16.MCRF4XX
deriving instance DecidableEq for crc16.RIELLO
deriving instance Repr for crc16.RIELLO
deriving instance DecidableEq for crc16.TMS37157
deriving instance Repr for crc16.TMS37157
deriving instance DecidableEq for crc16.USB
deriving instance Repr for crc16.USB
deriving instance DecidableEq for crc16.CRC_A
deriving instance Repr for crc16.CRC_A
deriving instance DecidableEq for crc16.KERMIT
deriving instance Repr for crc16.KERMIT
deriving instance DecidableEq for crc16.MODBUS
deriving instance Repr for crc16.MODBUS
deriving instance DecidableEq for crc16.X_25
deriving instance Repr for crc16.X_25
deriving instance DecidableEq for crc16.AUG_CCITT
deriving instance Repr for crc16.AUG_CCITT
deriving instance DecidableEq for crc16.BUYPASS
deriving instance Repr for crc16.BUYPASS
deriving instance DecidableEq for crc16.CCITT_FALSE
deriving instance Repr for crc16.CCITT_FALSE
deriving instance DecidableEq for crc16.CDMA2000
deriving instance Repr for crc16.CDMA2000
deriving instance DecidableEq for crc16.DDS_110
deriving instance Repr for crc16.DDS_110
deriving instance DecidableEq for crc16.DECT_R
deriving instance Repr for crc16.DECT_R
deriving instance DecidableEq for crc16.DECT_X
deriving instance Repr for crc16.DECT_X
deriving instance DecidableEq for crc16.EN_13757
deriving instance Repr for crc16.EN_13757
deriving instance DecidableEq for crc16.GENIBUS
deriving instance Repr for crc16.GENIBUS
deriving instance DecidableEq for crc16.T10_DIF
deriving instance Repr for crc16.T10_DIF
deriving instance DecidableEq for crc16.TELEDISK
deriving instance Repr for crc16.TELEDISK
deriving instance DecidableEq for crc16.XMODEM
deriving instance Repr for crc16.XMODEM
