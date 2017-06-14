/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.emit;

import static org.junit.Assert.*;
import org.junit.*;
import it.unibo.FOOL.test.*;

/*
 * Test: code generation issue when two irrelevant functions have the same name
 */

public final class FunNameConflictsTest extends UnitTest {
    @Test
    public void testFunNameConflicts() {
	prog = "let int f(int x) 1; in f(1);				\n"
		+ "let int f(int x) x; in f(2);				\n";
	result = 2;
	assertEquals(run(), result);
    }
}
