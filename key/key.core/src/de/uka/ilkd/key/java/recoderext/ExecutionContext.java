// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.PrettyPrinter;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.SourceVisitor;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;

public class ExecutionContext
extends JavaNonTerminalProgramElement 
implements Reference, TypeReferenceContainer, 
ExpressionContainer {

    private static final long serialVersionUID = 8575487220451641767L;

    /**
     * the ast parent
     */
    private NonTerminalProgramElement astParent;

    /**
     * the class context 
     */
    private TypeReference classContext;

    /**
     * the method signature of the currently active method
     */
    private MethodSignature methodContext;

    /**
     * the reference to the active object
     */
    private ReferencePrefix runtimeInstance;

    private TypeReference threadContext;
    private ReferencePrefix runtimeThread;

    protected ExecutionContext() {}

    /**
     * creates an execution context reference
     * @param classContext the TypeReference referring to the next enclosing
     * class 
     * @param methodContext the method signature representing the currently active method
     * @param runtimeInstance a ReferencePrefix to the object that
     * is currently active/executed
     */
    public ExecutionContext(TypeReference classContext,
                    MethodSignature methodContext,
                    ReferencePrefix runtimeInstance, TypeReference threadContext, ReferencePrefix runtimeThread) {
        this.classContext = classContext;
        this.methodContext = methodContext;
        this.runtimeInstance  = runtimeInstance;
        this.threadContext = threadContext;
        this.runtimeThread = runtimeThread;
        makeParentRoleValid();
    }

    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int count = 0;
        if (runtimeInstance != null) count++;
        if (classContext != null) count++;
        if (methodContext != null) count++;
        if (threadContext != null) count++;
        if (runtimeThread != null) count++;
        return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array.
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *    of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (classContext != null) {
            if (index == 0) return classContext;
            index--;
        }
        if (methodContext != null) {
            if (index == 0) return methodContext;
            index--;
        }
        if (runtimeInstance != null) {
            if (index == 0) return runtimeInstance;
            index--;
        }
        if (threadContext != null) {
            if (index == 0) return threadContext;
            index--;
        }
        if (runtimeThread != null) {
            if (index == 0) return runtimeThread;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Returns the positional code of the given child
     * @param child the exact child to look for.
     * @return the positional code of the given child, or <CODE>-1</CODE>.
     */
    public int getChildPositionCode(ProgramElement child) {
        int idx = 0;
        if (classContext != null) {
            if (child == classContext) return idx;
            idx ++;
        }
        if (methodContext != null) {
            if (child == methodContext) return idx;
            idx ++;
        }
        if (runtimeInstance != null) {
            if (child == runtimeInstance) return idx;
            idx ++;
        }
        if (threadContext != null) {
            if (child == threadContext) return idx;
            idx ++;
        }
        if (runtimeThread != null) {
            if (child == runtimeThread) return idx;
            idx ++;
        }
        return -1;
    }

    public void accept(SourceVisitor visitor) {       
    }

    public ExecutionContext deepClone() {
        return new ExecutionContext(classContext, methodContext, runtimeInstance, threadContext, runtimeThread);
    }

    public NonTerminalProgramElement getASTParent() {
        return astParent;
    }

    public void setParent(NonTerminalProgramElement parent) {
        astParent = parent;
    }

    public boolean replaceChild(recoder.java.ProgramElement child, 
                    recoder.java.ProgramElement newChild) {
        if (child == classContext) {
            classContext = (TypeReference) newChild;
        } else if (child == runtimeInstance) {
            runtimeInstance = (ReferencePrefix)newChild;
        } else {
            return false;
        }
        makeParentRoleValid();
        return true;
    }

    /**
     *      Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (classContext != null) {
            classContext.setParent(this);            
        }
        if (runtimeInstance != null) {
            ((Expression)runtimeInstance).setExpressionContainer(this);
        }
    }


    public TypeReference getTypeReferenceAt(int index) {
        if (classContext != null && index == 0) {
            return classContext;
        }
        if (threadContext != null && index == 1) {
            return threadContext;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
        int res = 0;
        if (classContext != null) res++;
        if (threadContext != null) res++;
        return res;
    }



    public Expression getExpressionAt(int index) {
        if (runtimeInstance != null && index == 0) {
            return (Expression) runtimeInstance;
        }
        if (runtimeThread != null && index == 1) {
            return (Expression) runtimeThread;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        int res = 0;
        if (runtimeInstance != null) res++;
        if (runtimeThread != null) res++;
        return res; 
    }


    /**
     * returns the type reference to the next enclosing class
     * @return the type reference to the next enclosing class
     */
    public TypeReference getTypeReference() {
        return classContext;
    }

    /**
     * returns the method signature of the currently active method
     * @return the method signature of the currently active method
     */
    public MethodSignature getMethodContext() {
        return methodContext;
    }


    /**
     * returns the runtime instance object
     * @return the runtime instance object
     */
    public ReferencePrefix getRuntimeInstance() {
        return runtimeInstance;
    }
    
    public TypeReference getThreadTypeReference() {
        return threadContext;
    }
    
    public ReferencePrefix getRuntimeThreadInstance() {
        return runtimeThread;
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
    }
}