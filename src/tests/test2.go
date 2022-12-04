package main
package main
import "fmt"

type int_variable struct{ s string, i int }

func incr(a int_variable) 
{
	{a.i=a.i+1}
}

func decr(a int_variable) 
{
	{a.i=a.i-1}
}

func somme(a,b int_variable)
{
	
	var c int_variable;
	c.s=a.s^"avec"^b.s;
	c.i=a.i+b.i;
	c
}

func main() {
	var a int_variable
	var b int_variable
	var c int_variable
	a.s="article 1"
	a.i=29
	b.s="article 2"
	b.i=56
	incr(a)
	incr(b)
	c=somme(a,b)
	fmt.Print("le prix de ", c.s, "est de", c.a)

}