// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.io.IOException;
import java.io.StringWriter;

import de.uka.ilkd.key.java.IStatementBlock;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;

public class DLProgramBlock {
    
    public static final DLProgramBlock EMPTY_JAVABLOCK
    	= new DLProgramBlock(new StatementBlock());
    private final IStatementBlock prg;


    /** create a new JavaBlock 
     * @param prg the root JavaProgramElement for this JavaBlock
     */
    private DLProgramBlock(IStatementBlock prg) {
	this.prg=prg;
    }

    /** create a new JavaBlock 
     * @param prg the root StatementBlock for this JavaBlock.
     * TacletIndex relies on <code>prg</code> being indeed a StatementBlock.
     */
    public static DLProgramBlock createJavaBlock(IStatementBlock prg) {
	assert prg != null;
	
	return new DLProgramBlock(prg);
    }
    

    public boolean isEmpty() {
	if (program() instanceof StatementContainer)  {
	    return size() == 0;
	}
	return this == EMPTY_JAVABLOCK;
    }
    
    public int size() {
	if ((program() instanceof StatementContainer))  {
	    return ((StatementContainer)program()).getChildCount();
	}
	return 0;
    }
    
    /** returns the hashCode */
    public int hashCode() {    	   
    	return 17 + ((program()==null) ? 0 : program().hashCode());
    }

    /** returns true iff the program elements are equal */
    public boolean equals(Object o) {
        if ( o == this ) {
            return true;
        } else if (!(o instanceof DLProgramBlock)) {
            return false;
        } else {
            DLProgramBlock block = (DLProgramBlock)o;
            
            if(block.program() == null){
        	return program()==null;
            }
            else{
        	return block.program().equals(program());
            }
        } 
    }

    /** returns true if the given ProgramElement is equal to the
     * one of the JavaBlock modulo renaming (see comment in SourceElement)
     */ 
    public boolean equalsModRenaming(Object o, 
				     NameAbstractionTable nat) {
        if (!(o instanceof DLProgramBlock)) {
            return false;
        }       
        return equalsModRenaming(((DLProgramBlock)o).program(), nat);
    }


    /** returns true if the given ProgramElement is equal to the
     * one of the JavaBlock modulo renaming (see comment in SourceElement)
     */ 
    private boolean equalsModRenaming(ProgramElement pe,
				     NameAbstractionTable nat) {
	if (pe == null && program() == null) {
	    return true;
	} else if (pe != null && program() != null) {	    
	    return program().equalsModRenaming(pe, nat);	   
	}
        return false;
    }

    /** returns the java program 
     * @return the stored JavaProgramElement
     */
    public ProgramElement program() {
	return prg;
    }

    /** toString */
    public String toString() {
	//if (this==EMPTY_JAVABLOCK) return "";
	StringWriter sw=new StringWriter();
	try {
	    PrettyPrinter pp=new PrettyPrinter(sw, true);
	    pp.setIndentationLevel(0);
	    prg.prettyPrint(pp);
	} catch (IOException e) {
	    System.err.println("toString of JavaBlock failed due to :"+e);
	    e.printStackTrace();
	}
	return sw.toString();
    }

}
