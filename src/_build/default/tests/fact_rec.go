package main
import ” fmt ”
// v e r s i o n r e c u r s i v e de l a f a c t o r i e l l e
funcfact(nint) int {
if n<= 1 {
return 1 ;
}
return n∗fact(n −1);
}
funcmain(){
for n:= 0 ; n <= 10 ; n++{
fmt.Print(fact(n));
fmt.Print(”\n”)
}
}
