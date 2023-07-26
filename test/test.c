#include <stdbool.h>
extern int unknown1(void);
extern int unknown2(void);
extern void assert(bool);

int main()
{
	int x = 0;
	int y = 0;
	for (int i = 0; i < 100; i++) {
		if (i % 2 == 0) {
			x++;
		} else {
			y++;
		}
	}
	assert(x + y == 100);
	// unsigned int x = 0;
	// unsigned int y = 10;
	// unsigned int z=5000000;
	// while(x<z){	
	// 	x += 2;
	// 	y += 5;
	// }
	// // assert(x == z);
	// assert(y % 5 == 0);
	// return 0;
}