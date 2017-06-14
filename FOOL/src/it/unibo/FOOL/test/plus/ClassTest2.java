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
 * OO Test #2: simple class definitions with slots
 */
public final class ClassTest2 extends UnitTest {
    @Test
    public void testClass2() {
	prog = "class a(int x1) = object int x; int y = 6; end;"
		+ "\n class b = object inherit a(1); int z = 2; end; new b().y;\n";
	result = 6;
	trace = true;
	assertEquals(run(), result);
    }
}
