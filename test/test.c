#include <stdbool.h>
extern int unknown1(void);
extern int unknown2(void);
extern void assert(bool);

int main()
{
	unsigned int x = 0;
	unsigned int y = 10000000;
	unsigned int z=5000000;
	while(x<y){	
		if(x>=5000000)
			z--;
		x++;
	}
	assert(z==0);
	return 0;
}