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
 * OO Test #6: chain of slots
 */
public final class ClassTest6 extends UnitTest {
    @Test
    public void testClass6() {
	prog = "   class inner = object int x = 5; end;					\n"
		+ "class outer = object inner y = new inner; end;			\n"
		+ "let outer o = new outer; in o.y.x; \n";
	result = 5;
	assertEquals(run(), result);
    }
}
