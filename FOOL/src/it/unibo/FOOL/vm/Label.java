/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.vm;

/***
 * Excerpted from "Language Implementation Patterns",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book information.
***/

import java.util.*;

public class Label {
    String name;
    int address;
    boolean isForwardRef = false;
    boolean isDefined = false;
    Vector<Integer> forwardReferences = null;

    public Label(String name) { this.name = name; }

    public void addForwardReference(int address) {
        if (forwardReferences == null)
            forwardReferences = new Vector<Integer>();
        forwardReferences.addElement(new Integer(address));
    }

    public void resolveForwardReferences(byte[] code) {
        isForwardRef = false;
        Vector<Integer> oprandsToPatch = forwardReferences;
        for (int addrToPatch : oprandsToPatch) {
            Assembler.writeInt(code, addrToPatch, address);
        }
    }

    public int hashCode() { return name.hashCode(); }
    public String toString() {
        String refs = "";
        if (forwardReferences != null)
            refs = "[refs=" + forwardReferences.toString() + "]";
        return name + "@" + address + refs;
    }
}
