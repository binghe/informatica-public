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
 * OO Test #6: overloading of parent slots
 */

public final class ClassTest7 extends UnitTest {
    @Test
    public void testClass6() {
	prog = "   class A = object int x = 5; end;					\n"
		+ "class B = object inherit A; int x = 3; int y = 2; end;		\n"
		+ "let A a = new B; in a.x; \n";
	result = 3;
	assertEquals(run(), result);
    }
}
