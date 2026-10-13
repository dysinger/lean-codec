# extern-c-fast-path

Speed up the encode/decode hot paths maximally with trusted `@[extern]` C patches
(a `uint8_t *`+`size_t` full-consumption loop and slice results), landing this
stopgap **before** the full GC-less C extraction backend (`compiler-tier-extraction`).
