#include <stdbool.h>
extern int unknown1(void);
extern int unknown2(void);
extern void assert(bool);

int main() {
    int x = unknown1();
    int y = unknown2();
    int x0 = x;
    int y0 = y;
    // if (x > 0) {
    //     y = y + 1;
    //     x = x - 1;
    // } else {
    //     y = y - 1;
    //     x = x + 1;
    // }
    // assert(x + y == x0 + y0);
    if (x > 0) {
        for (int i = 0; i < x0; i++) {
            x++;
            y += 2;
            assert(x == x0 + x0);
        }
        // assert(x == x0 + x0);
    }
    // assert(x == x0);
    // assert(y + x == x0 + y0 + 3);
    // if (x < 0) {
    //     x++;
    // } else {
    //     x--;
    // }
    // assert(x + y == x0 + y0 + 1 || x + y == x0 + y0 - 1);
    // while (i < 10000) {
    //     if (x < 5000) {
    //         x = x + 1;
    //     } else {
    //         x = x + 2;
    //         y++;
    //     }
    //     i++;
    // }
    return x + y;
}