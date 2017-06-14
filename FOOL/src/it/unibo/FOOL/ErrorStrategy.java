/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL;

/***
 * Excerpted from "The Definitive ANTLR 4 Reference",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpantlr2 for more book information.
***/

import org.antlr.v4.runtime.*;

public class ErrorStrategy extends DefaultErrorStrategy {
    /*
     * Instead of recovering from exception e, re-throw it wrapped in a generic
     * RuntimeException so it is not caught by the rule function catches.
     * Exception e is the "cause" of the RuntimeException.
     */
    public void recover(Parser recognizer, RecognitionException e) {
	throw new RuntimeException(e);
    }

    /*
     * Make sure we don't attempt to recover inline; if the parser successfully
     * recovers, it won't throw an exception.
     */
    public Token recoverInline(Parser recognizer) throws RecognitionException {
	throw new RuntimeException(new InputMismatchException(recognizer));
    }

    /* Make sure we don't attempt to recover from problems in subrules. */
    public void sync(Parser recognizer) {
    }
}
