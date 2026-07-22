D7 gate spike (see docs/migration/reports/T0-smt-spike.md). Build/run needs the brew z3:

    Z3_SYS_Z3_HEADER=/opt/homebrew/opt/z3/include/z3.h Z3_LIBRARY_PATH_OVERRIDE=/opt/homebrew/opt/z3/lib cargo run --release
