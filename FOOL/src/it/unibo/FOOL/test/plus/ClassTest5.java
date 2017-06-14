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
 * OO Test #5: accessing parent slots + class def with init pars
 */

public final class ClassTest5 extends UnitTest {
    @Test
    public void testClass5() {
	prog = "class C1 (int x0) = object int x = x0; end; \n"
		+ "class C2 (int y0) = object inherit C1 (y0); int y = y0 + 1; end; \n"
		+ "let C2 o = new C2(5); in o.x; \n";
	result = 5;
	trace = true;
	assertEquals(run(), result);
    }
}
