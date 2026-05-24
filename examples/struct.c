#include <stdlib.h>
#include <assert.h>

typedef struct {
	int fst;
	int snd;
} coord_t;


int foo(coord_t *c, int z) {
	assert(z != -1);
	return c->fst + c->snd + z;
}

int wrapper(coord_t * c, int fst, int snd, int z) {
	if (c != NULL) {
		c->fst = fst;
		c->snd = snd;
	}
	return foo(c, z);
}

int main() {
	coord_t c = { 1, 2 };
	wrapper(&c, c.fst, c.snd, 2);
	foo(&c, 2);
	return EXIT_SUCCESS;
}
