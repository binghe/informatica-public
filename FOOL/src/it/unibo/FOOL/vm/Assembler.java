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

/*
 * Modified by Chun Tian, for programmatically generating assembly code in Java.
 */

import java.util.*;

public class Assembler {
    public static final int INITIAL_CODE_SIZE = 1024;

    protected Map<String, Integer> instructionOpcodeMapping =
    		new HashMap<String, Integer>();

    protected Map<String, Label> labels = new HashMap<String, Label>();
    protected List<Object> constPool = new ArrayList<Object>();
    protected int ip = 0; // Instruction address pointer; used to fill code
    protected byte[] code = new byte[INITIAL_CODE_SIZE]; // code memory
    protected int dataSize = 0;
    protected int nlocals = 0;
    protected Function mainFunction = null;

    public Assembler() {
    	Bytecode.Instruction[] instructions = Bytecode.instructions;
    	for (int i = 1; i < instructions.length; i++)
    		instructionOpcodeMapping.put(instructions[i].name.toLowerCase(), i);
    }

    public byte[] getMachineCode() { return code; }
    public int getCodeMemorySize() { return ip; }
    public int getDataSize() { return dataSize; }
    public int getLocals() { return nlocals; }
    public Function getMainFunction() { return mainFunction; }

    protected void ensureCapacity(int index) {
        if (index >= code.length) { // expand
            int newSize = Math.max(index, code.length) * 2;
            byte[] bigger = new byte[newSize];
            System.arraycopy(code, 0 , bigger, 0, code.length);
            code = bigger;
        }
    }

    /* Generate code for an instruction with no operands */
    public void gen(String instrName) {
        Integer opcodeI = instructionOpcodeMapping.get(instrName);
        if (opcodeI == null) {
            System.err.println("line " + ip +
                               ": Unknown instruction: " + instrName);
            return;
        }
        int opcode = opcodeI.intValue();
        ensureCapacity(ip + 1);
        code[ip++] = (byte)(opcode & 0xFF);
    }

    /* Generate code for an instruction with one operand */
    public void gen(String instrName, Object operand) {
        gen(instrName);
        genOperand(operand);
    }

    public void gen(String instrName, Object o1, Object o2) {
        gen(instrName, o1);
        genOperand(o2);
    }

    public void gen(String instrName, Object o1, Object o2, Object o3) {
        gen(instrName, o1, o2);
        genOperand(o3);
    }

    protected void genOperand(Object operand) {
    	int v = 0;
    	if (operand instanceof Integer)
    		v = ((Integer) operand).intValue();
    	else if (operand instanceof Label)
    		v = getLabelAddress((Label) operand);
    	else if (operand instanceof Function)
    		v = getConstantPoolIndex(operand);
    	else
    		System.err.println("line " + ip +
    						   ": Unknown operand: " + operand);
        ensureCapacity(ip + 4);	// expand code array if necessary
        writeInt(code, ip, v);	// write operand to code byte array
        ip += 4;				// we've written four bytes
    }

    protected int getRegisterNumber(String rs) {
        rs = rs.substring(1); // convert "rN" -> N
        return Integer.valueOf(rs);
    }

    /* After parser is complete, look for unresolved labels */
    public void check() {
        for (String name : labels.keySet()) {
            Label sym = (Label) labels.get(name);
            if (sym.isForwardRef)
                System.err.println("unresolved reference: " + name);
        }
    }

    public Label newLabel(String id) {
    	Label sym = (Label) labels.get(id);
        if (sym == null) {
        	Label l = new Label(id);	// isDefined: false, isForwardRef: false
        	labels.put(id, l);
        	return l;
        } else
        	return newLabel(id + "'");	// generate new unique labels
    }

    public void setLabel(Label label) {
    	String id = label.name;
        Label sym = (Label) labels.get(id);
        assert (label == sym);

        if (sym.isDefined == false) {
        	sym.isDefined = true;
        	sym.address = ip;
        }

        if (sym.isForwardRef) // we have found definition of forward
        	sym.resolveForwardReferences(code);
        else
        	System.err.println("line " + ip +
        					   ": redefinition of symbol " + id);
    }

    /* Compute the code address of a label */
    protected int getLabelAddress(Label label) {
    	String id = label.name;
        Label sym = (Label) labels.get(id);
        assert (label == sym);

        if (sym.isDefined == false) {
            // assume it's a forward code reference; record operand address
        	sym.isForwardRef = true;
        	sym.addForwardReference(ip);
        	return 0; // we don't know the real address yet
        }
        else
        	return sym.address;
    }

    protected int getConstantPoolIndex(Object o) {
        if (constPool.contains(o))
        	return constPool.indexOf(o);
        constPool.add(o);
        return constPool.size() - 1;
    }

    public Object[] getConstantPool() { return constPool.toArray(); }

    public void defineFunction(String name, int args, int locals) {
        Function f = new Function(name, args, locals, ip);
        if (name.equals("main"))
        	mainFunction = f;
        // Did someone referred to this function before it was defined?
        // if so, replace element in constant pool (at same index)
        if (constPool.contains(f))
        	constPool.set(constPool.indexOf(f), f);
        else
        	getConstantPoolIndex(f); // save into constant pool
    }

    protected int getFunctionIndex(String id) {
        int i = constPool.indexOf(new Function(id));
        if (i >= 0)
        	return i; // already in system; return index.
        // must be a forward function reference
        // create the constant pool entry; we'll fill in later
        return getConstantPoolIndex(new Function(id));
    }

    public void defineDataSize(int n) { dataSize = n; }
    public void setLocals(int n) { nlocals = n; }

    public static int getInt(byte[] memory, int index) {
        int b1 = memory[index++] & 0xFF; // mask off sign-extended bits
        int b2 = memory[index++] & 0xFF;
        int b3 = memory[index++] & 0xFF;
        int b4 = memory[index++] & 0xFF;
        int word = b1 << (8*3) | b2 << (8*2) | b3 << (8*1) | b4;
        return word;
    }

    /* Write value at index into a byte array, highest to lowest byte,
     * left to right.
     */
    public static void writeInt(byte[] memory, int index, int value) {
        memory[index++] = (byte)((value >> (8*3)) & 0xFF); // get highest byte
        memory[index++] = (byte)((value >> (8*2)) & 0xFF);
        memory[index++] = (byte)((value >> (8*1)) & 0xFF);
        memory[index++] = (byte)(value & 0xFF);
    }
}
