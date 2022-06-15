let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_LIN_STRM : RVInstS<2, OPC_CUSTOM_1,
                    (outs ),
                    (ins GPR:$rs1),
                    "ss_lin_strm", "$rs1">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_IND_STRM : RVInstS<2, OPC_CUSTOM_2,
                    (outs ),
                    (ins GPR:$rs1),
                    "ss_ind_strm", "$rs1">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_WR_RD : RVInstS<2, OPC_CUSTOM_3,
                    (outs ),
                    (ins GPR:$rs1),
                    "ss_wr_rd", "$rs1">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CFG_PORT : RVInstS<2, OPC_CUSTOM_0,
                    (outs ),
                    (ins GPR:$rs1, simm12:$simm12),
                    "ss_cfg_port", "$rs1, $simm12">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CFG_PARAM : RVInstS<3, OPC_CUSTOM_0,
                    (outs ),
                    (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                    "ss_cfg_param", "$rs1, $rs2, $simm12">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_STAT : RVInstI<6, OPC_CUSTOM_2,
                    (outs GPR:$rd),
                    (ins GPR:$rs1, simm12:$simm12),
                    "ss_stat", "$rd, $rs1, $simm12">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_WAIT : RVInstI<6, OPC_CUSTOM_1,
                    (outs GPR:$rd),
                    (ins GPR:$rs1, simm12:$simm12),
                    "ss_wait", "$rd, $rs1, $simm12">,
                    Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_RECV : RVInstI<6, OPC_CUSTOM_0,
                    (outs GPR:$rd),
                    (ins GPR:$rs1, simm12:$simm12),
                    "ss_recv", "$rd, $rs1, $simm12">,
                    Sched<[SSRead, SSWrite]>;

