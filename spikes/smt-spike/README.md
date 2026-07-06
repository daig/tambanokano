D7 gate spike (see docs/migration/reports/T0-smt-spike.md). Build/run needs the brew z3:

    Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h RUSTFLAGS="-L /opt/homebrew/lib" cargo run --release
