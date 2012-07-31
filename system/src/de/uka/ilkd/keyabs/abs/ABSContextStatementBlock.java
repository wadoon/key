// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.IContextStatementBlock;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/** 
 * In the DL-formulae description of Taclets the program part can have
 * the following form < pi alpha;...; omega > Phi where pi is a prefix
 * consisting of open brackets, try's and so on and omega is the rest
 * of the program. Between the prefix pi and the postfix omega there
 * can stand an arbitrary program. This pattern is realized using this
 * class.
 */

public class ABSContextStatementBlock extends ABSStatementBlock implements IContextStatementBlock {


    public ABSContextStatementBlock(IABSStatement s) {
        super(s);
    }
    
    public ABSContextStatementBlock(IABSStatement[] body) {
        super(body);
    }

    public ABSContextStatementBlock(ImmutableArray<? extends IABSStatement> body) {
    	super(body);
    }

	@Override
    public boolean requiresExplicitExecutionContextMatch() {
    	return false;
    }

    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
    */

    @Override
    public int getChildCount() {
	int count = 0;
	count += super.getChildCount();
        return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     * of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
	return super.getChildAt(index);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    @Override
    public void visit(ABSVisitor v) {
    	v.performActionOnABSContextStatementBlock(this);
    }
    
    /* toString */
    @Override
    public String toString() {
	StringBuilder result = new StringBuilder();
	result.append("{.. \n");
	printBody(result);
	result.append("...}");
	return result.toString();
    }

    /**
     * overrides the check of the superclass as unmatched elements will disappear in 
     * the suffix of this ContextStatementBlock
     */
    @Override
    public boolean compatibleBlockSize(int pos, int max) {
        return true;
    }        
    
    
    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        SourceData newSource = source;
        
        if (matchCond.getInstantiations().
                getContextInstantiation() != null) {
            // Currently we do not allow to context statement block 
            // occurrences in find or assumes clauses
            return null;
        }
        
        final ProgramElement src = newSource.getSource();
        final IServices services  = source.getServices();
        
        ExecutionContext lastExecutionContext = null;
               
        final ProgramPrefix prefix;
        int pos = -1;
        PosInProgram relPos = PosInProgram.TOP;                         
        
        if (src instanceof ProgramPrefix) {
            prefix = (ProgramPrefix)src;            
            final int srcPrefixLength     = prefix.getPrefixLength();
            final int patternPrefixLength = getPrefixLength();
                        
            if (patternPrefixLength > srcPrefixLength) {
                Debug.out("Program match FAILED. Source has not enough prefix elements.", 
                        this, source);
                return null;
            }
     
            pos = srcPrefixLength - patternPrefixLength;
            
            ProgramPrefix firstActiveStatement = prefix.getPrefixElementAt(pos);                                                                                            
            
            relPos = firstActiveStatement.getFirstActiveChildPos();
            
            // firstActiveStatement contains the ProgramPrefix in front of the first active statement
            // start denotes the child where to start to match
            // in some cases firstActiveStatement already denotes the element to match
            // (empty block, empty try block etc.) this is encoded by setting start to -1
            int start = -1;
            
            if (relPos != PosInProgram.TOP) {                
                start = relPos.get(relPos.depth()-1);                                                    
                if (relPos.depth()>1) {
                    firstActiveStatement = (ProgramPrefix)
                      PosInProgram.getProgramAt(relPos.up(), 
                              firstActiveStatement);
                }
            }
            newSource = new SourceData(firstActiveStatement, start, services);                        
        } else {
            prefix = null;
        }
                
        // matching children
        matchCond = matchChildren(newSource, matchCond, 0); 
        
        if (matchCond == null) {
            return null;
        }
            
        matchCond = makeContextInfoComplete(matchCond,
        				    newSource, 
        				    prefix, 
        				    pos, 
        				    relPos, 
        				    src,
        				    services);
        
        if (matchCond == null) {
            return null;
        }       
        
        Debug.out("Successful match.");
        return matchCond;
    }

    /**
     * completes match of context block by adding the prefix end position
     * and the suffix start position
     */
    private MatchConditions makeContextInfoComplete(
	    MatchConditions matchCond, 
            SourceData newSource, 
            ProgramPrefix prefix, 
            int pos, 
            PosInProgram relPos, 
            ProgramElement src,
            IServices services) {
        
        final SVInstantiations instantiations = matchCond.getInstantiations();        
        final ExecutionContext lastExecutionContext = instantiations.getExecutionContext();
       
        final PosInProgram prefixEnd = matchPrefixEnd(prefix, pos, relPos);
        
        // compute position of the first element not matched        
        final int lastMatchedPos = newSource.getChildPos();                
        final PosInProgram suffixStart = prefixEnd.up().down(lastMatchedPos); 
                
        /** add context block instantiation */
        matchCond = matchCond.setInstantiations
            (instantiations.replace(prefixEnd, 
        	    		    suffixStart, 
        	    		    lastExecutionContext, 
        	    		    src,
        	    		    services));
        return matchCond;
    }

    /**
     * computes the PosInProgram of the first element, which is not part of the prefix
     * @param prefix the ProgramPrefix the outer most prefix element of the source
     * @param pos the number of elements to disappear in the context
     * @param relPos the position of the first active statement of element
     *  prefix.getPrefixElementAt(pos);
     * @return the PosInProgram of the first element, which is not part of the prefix
     */
    private PosInProgram matchPrefixEnd(final ProgramPrefix prefix, int pos, PosInProgram relPos) {
        PosInProgram prefixEnd = PosInProgram.TOP;
        if (prefix != null) {            
            final IntIterator[] iterators = new IntIterator[pos + 1];
            iterators[pos] = relPos.iterator();
            
            for (int i = pos - 1; i>=0; i--) {
                final ProgramPrefix prefixEl = prefix.getPrefixElementAt(i);                          
                iterators[i] = prefixEl.getFirstActiveChildPos().iterator();               
            }

            for (final IntIterator it : iterators) {
                while (it.hasNext()) {
                    prefixEnd = prefixEnd.down(it.next());
                }
            }
        } else {
            prefixEnd = relPos;
        }
        return prefixEnd;
    }

	@Override
	public IExecutionContext getExecutionContext() {
		return null;
	}
}
