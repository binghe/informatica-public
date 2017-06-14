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
 * OO Test #1: simple class definitions
 */
public final class ClassTest1 extends UnitTest {
    @Test
    public void testClass1() {
	prog = "class a = object end;\n class b = object inherit a; end; 5;\n";
	result = 5;
	assertEquals(run(), result);
    }
}
