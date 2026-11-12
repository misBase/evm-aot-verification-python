theory Params
  imports
    Main
begin

definition Gzero  :: "int"  where 
"Gzero = 0"

definition Gquickstep  :: "int"  where 
"Gquickstep = 2"

definition Gfasteststep  :: "int"  where 
"Gfasteststep = 3"

definition Gfastishstep  :: "int"  where 
"Gfastishstep = 4"

definition Gfaststep  :: "int"  where 
"Gfaststep = 5"

definition Gmidstep  :: "int"  where 
"Gmidstep = 8"

definition Gslowstep  :: "int"  where 
"Gslowstep = 10"

definition Gextstep  :: "int"  where 
"Gextstep = 20"

definition homestead_block  :: "int"  where 
"homestead_block = 1150*1000"

definition Gjumpdest  :: "int"  where 
"Gjumpdest = 1"

definition Gsset  :: "int"  where 
"Gsset = 20000"

definition Gsreset  :: "int"  where 
"Gsreset = 5000"

definition Rsclear  :: "int"  where 
"Rsclear = 15000"

definition Rsuicide  :: "int"  where 
"Rsuicide = 24000"

definition Gcreate  :: "int"  where 
"Gcreate = 32000"

definition Gcreate2 :: "int"  where
"Gcreate2 = 32000"

definition Gcodedeposit  :: "int"  where 
"Gcodedeposit = 200"

definition Gcallvalue  :: "int"  where 
"Gcallvalue = 9000"

definition Gcallstipend  :: "int"  where 
"Gcallstipend = 2300"

definition Gnewaccount  :: "int"  where 
"Gnewaccount = 25000"

definition Gexp  :: "int"  where 
"Gexp = 10"

definition Gmemory  :: "int"  where 
"Gmemory = 3"

definition Gtxdatazero  :: "int"  where 
"Gtxdatazero = 4"

definition Gtxdatanonzero  :: "int"  where 
"Gtxdatanonzero = 68"

definition Gtransaction  :: "int"  where 
"Gtransaction = 21000"

definition Glog  :: "int"  where 
"Glog = 375"

definition Glogdata  :: "int"  where 
"Glogdata = 8"

definition Glogtopic  :: "int"  where 
"Glogtopic = 375"

definition Gsha3  :: "int"  where 
"Gsha3 = 30"

definition Gsha3word  :: "int"  where 
"Gsha3word = 6"

definition Ginitcodeword  :: "int"  where
"Ginitcodeword = 2"

definition Gcopy  :: "int"  where 
"Gcopy = 3"

definition Gblockhash  :: "int"  where 
"Gblockhash = 20"

definition Gmcopy :: "int" where
"Gmcopy = 3"

definition Greturn :: "int" where
"Greturn = 0"

definition Grevert :: "int" where
"Grevert = 0"

definition MemoryGas :: "int" where
"MemoryGas = 3"

definition QuadCoeffDiv :: "int" where
"QuadCoeffDiv = 512"

definition MaxWordSize :: "int" where
"MaxWordSize = 0x1FFFFFFFE0"

definition WarmStorageReadCostEIP2929:: "int" where
"WarmStorageReadCostEIP2929 = 100"

definition Gtload :: "int" where
"Gtload = WarmStorageReadCostEIP2929"

definition Gtstore :: "int" where 
"Gtstore = WarmStorageReadCostEIP2929"

definition MaxCodeSize :: "int" where
"MaxCodeSize = 24576"

definition MaxInitCodeSize :: "int" where
"MaxInitCodeSize = 2 * MaxCodeSize"

end