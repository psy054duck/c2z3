#include <stdbool.h>
extern int unknown1();
extern int unknown2();
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
    for (int i = 0; i < 100; i++) {
        x++;
        y += 2;
    }
    assert(x == x0 + 100);
    // if (x < 0) {
    //     x++;
    // } else {
    //     x--;
    // }
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