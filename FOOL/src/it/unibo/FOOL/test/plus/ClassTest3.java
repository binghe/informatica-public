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
 * OO Test #3: accessing local slots
 */
public final class ClassTest3 extends UnitTest {
    @Test
    public void testClass3() {
	prog = "class C = object int x = 5; end; let C o = new C; in o.x; \n";
	result = 5;
	trace = true;
	assertEquals(run(), result);
    }
}
