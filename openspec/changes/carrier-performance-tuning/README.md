# carrier-performance-tuning

Profile the single-carrier codec, attribute the cost on the `Bytes n` carrier, re-stage the hot encode/decode loops and tune the C compiler flags to approach hand-tuned C encoding/decoding throughput. (Formerly `llvm-performance-tuning`; §0 measured LLVM as neutral and removed the override, so the remaining work is pure lowering + flag tuning, not LLVM utilization.)
