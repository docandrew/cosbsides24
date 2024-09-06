// read in a number from a CLI flag, double it and print the output

package main

import (
	"fmt"
	"os"
	"strconv"
)

func timestwo(n int) int {
	return n * 2
}

func main() {
	n, _ := strconv.Atoi(os.Args[1])
	fmt.Printf("%d * 2 = %d\n", n, timestwo(n))
}
