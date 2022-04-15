// Intrinsics marks the temporal region scope
def int_ss_temporal_region_start : Intrinsic<[llvm_ptr_ty],
                                             [],
                                             [IntrWillReturn]>;
def int_ss_temporal_region_end   : Intrinsic<[],
                                             [llvm_ptr_ty],
                                             []>;

// Intrinsics marks the DFGs coexist on the CGRA
def int_ss_config_start : Intrinsic<[llvm_ptr_ty],
                                    [],
                                    [IntrWillReturn]>;
def int_ss_config_end   : Intrinsic<[],
                                    [llvm_ptr_ty],
                                    []>;

// Intrinsic marks the array to be fifo-ized
def int_ss_fifo : Intrinsic<[],
			    [llvm_ptr_ty, llvm_i64_ty],
			    []>;

// Intrinsic marks the size of an ss-involved array
def int_ss_array : Intrinsic<[],
			     [llvm_ptr_ty, llvm_i64_ty],
			     []>;
