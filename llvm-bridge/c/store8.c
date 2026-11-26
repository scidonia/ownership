/* The one-byte store kernel: `p[i] = v` for a uint8_t pointer. */
#include <stdint.h>

void store8(uint8_t *p, uint64_t i, uint8_t v) {
  p[i] = v;
}
