# compiler-tier-extraction

Author a buffer/no-GC extraction tier so the ByteArray run-model lowers to uint8_t*-based C with no per-byte boxing, and benchmark it against hand-tuned parsers.
