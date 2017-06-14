/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.*;
import org.junit.*;

public final class RecursiveTest extends UnitTest {
    @Test
    public void testRecursiveFunction() {
	prog = "let int fact(int n)					\n"
		+ "     if (n==1) then {1} else {n*fact(n + -1)};	\n"
		+ " in fact(10);						\n";
	result = 3628800;
	trace = true;
	tail_rec = true;
	assertEquals(run(), result);
    }
}
