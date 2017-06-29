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
 * Polymorphic Type Test #6: no applicable method
 */

public final class PolymorphicTest6 extends UnitTest {
    @Test
    public void testPolymorphicType() {
	prog = "   class A = object end;				\n"
		+ "class B = object inherit A; end;			\n"
		+ "let int foo(A o1, B o2) 2;				\n"
		+ "    int foo(B o1, A o2) 3;				\n"
		+ "    int foo(B o1, B o2) 4;				\n"
		+ "    A obj = new A();					\n"
		+ "in obj.foo(obj) + 6;					\n";
	try {
	    compile();
	} catch (Exception e) {
	    assertTrue(e instanceof RuntimeException);
	}
    }
}
