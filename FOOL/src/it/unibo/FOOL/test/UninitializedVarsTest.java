/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.assertTrue;
import org.junit.Test;

public class UninitializedVarsTest extends UnitTest {
    @Test
    public void testUninitializedVars() {
	prog = "class C = object int x; end; let C o = new C(); in o.x;\n";
	trace = true;
	try {
	    run();
	} catch (Exception e) {
	    assertTrue(e instanceof RuntimeException);
	}
    }
}
