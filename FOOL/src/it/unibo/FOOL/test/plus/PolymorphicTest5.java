/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

import static org.junit.Assert.*;
import org.junit.*;
import it.unibo.FOOL.test.*;

/*
 * Polymorphic Type Test #5: classic multimethods with if..then..else inside
 */

public final class PolymorphicTest5 extends UnitTest {
    @Test
    public void testPolymorphicType() {
	prog = "   class A = object end;				\n"
		+ "class B = object inherit A; end;			\n"
		+ "let int foo(A o1, A o2) 1;				\n"
		+ "    int foo(A o1, B o2) 2;				\n"
		+ "    int foo(B o1, A o2) 3;				\n"
		+ "    int foo(B o1, B o2) 4;				\n"
		+ "    bool flag = false;				\n"
		+ "    A obj = (if flag then {new A()} else {new B()}); \n"
		+ "in obj.foo(obj) + 6;					\n";
	result = 10;
	// trace = true;
	assertEquals(run(), result);
    }
}
