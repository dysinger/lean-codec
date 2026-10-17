# carrier-performance-tuning

Profile the single-carrier codec, attribute the cost on the `Bytes n` carrier, and re-stage the bulk encode/decode hot loops through a law-backed `ByteArray` accumulator + tuned C flags to approach hand-tuned C throughput.
