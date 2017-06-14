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
 * Method Test #5: methods at different levels
 */

public class MethodTest6 extends UnitTest {
    @Test
    public void testMethod5() {
	prog = "let int f(bool b)						\n"
		+ "     let int y = 10;						\n"
		+ "         int f(int x) x+y;					\n"
		+ "     in (if b then {f(false)} else {f(2)});			\n"
		+ " in f(true);							\n";
	result = 12;
	trace = true;
	assertEquals(run(), result);
    }
}
