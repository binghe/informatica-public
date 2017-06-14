/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import it.unibo.FOOL.test.*;

/*
 * OO Test #4: accessing parent slots
 */
public final class ClassTest4 extends UnitTest {
    @Test
    public void testClass4() {
	prog = "class C1 = object int x = 5; end; " + "class C2 = object inherit C1; int y = 2; end; "
		+ "let C2 o = new C2; in o.x; \n";
	result = 5;
	trace = true;
	assertEquals(run(), result);
    }
}
