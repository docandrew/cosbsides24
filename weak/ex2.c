#include <stdio.h>
#include <stdlib.h>

int timestwo(int x) {
    return x * 2;
}

int main(int argc, char **argv) {
    // get input from user and double it
    int x = atoi(argv[1]);
    int y = timestwo(x);
    printf("%d * 2 is %d\n", x, y);
    return 0;
}