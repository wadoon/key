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
import de.uka.ilkd.key.java.IStatementBlock;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.Debug;

/**
 * Statement block. taken from COMPOST and changed to achieve an immutable
 * structure
 */

public class ABSStatementBlock extends ABSNonTerminalProgramElement implements
        StatementContainer, IABSStatement, ProgramPrefix, IStatementBlock {

    /**
     * Body.
     */
    private final ImmutableArray<? extends IABSStatement> body;

    /**
     * contains all program prefix elements below and including itself
     */
    private final ImmutableArray<ProgramPrefix> prefixElementArray;

    private PosInProgram firstActiveChildPos = null;

    public ABSStatementBlock() {
        body = new ImmutableArray<IABSStatement>();
        prefixElementArray = new ImmutableArray<ProgramPrefix>(this);
    }

    public ABSStatementBlock(ImmutableArray<? extends IABSStatement> as) {
        // check for non-null elements (bug fix)
        Debug.assertDeepNonNull(as, "statement block contructor");
        body = as;
        prefixElementArray = computePrefixElements(body);
    }

    public ABSStatementBlock(IABSStatement as) {
        this(new ImmutableArray<IABSStatement>(as));
    }

    public ABSStatementBlock(IABSStatement[] body) {
        this(new ImmutableArray<IABSStatement>(body));
    }

    private ImmutableArray<ProgramPrefix> computePrefixElements(
            ImmutableArray<? extends IABSStatement> b) {
        return computePrefixElements(b, 0, this);
    }

    /** computes the prefix elements for the given array of statment block */
    public static ImmutableArray<ProgramPrefix> computePrefixElements(
            ImmutableArray<? extends IABSStatement> b, int offset,
            ProgramPrefix current) {
        final ProgramPrefix[] pp;

        if (b.size() > 0 && b.get(0) instanceof ProgramPrefix) {
            final ProgramPrefix prefixElement = (ProgramPrefix) b.get(0);

            final int prefixLength = ((ProgramPrefix) b.get(0))
                    .getPrefixLength();
            pp = new ProgramPrefix[prefixLength + 1];
            prefixElement.getPrefixElements().arraycopy(offset, pp, 1,
                    prefixLength);
        } else {
            pp = new ProgramPrefix[1];
        }
        pp[0] = current;
        return new ImmutableArray<ProgramPrefix>(pp);
    }

    /**
     * Get body.
     * 
     * @return the statement array wrapper.
     */

    @Override
    public ImmutableArray<? extends IABSStatement> getBody() {
        return body;
    }

    public boolean isEmpty() {
        return body.size() == 0;
    }

    /**
     * Returns the number of children of this node.
     * 
     * @return an int giving the number of children of this node
     */

    @Override
    public int getChildCount() {
        return body.size();
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child
     * array
     * 
     * @param index
     *            an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *                if <tt>index</tt> is out of bounds
     */

    @Override
    public ProgramElement getChildAt(int index) {
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of statements in this container.
     * 
     * @return the number of statements.
     */

    @Override
    public int getStatementCount() {
        return body.size();
    }

    /*
     * Return the statement at the specified index in this node's "virtual"
     * statement array.
     * 
     * @param index an index for a statement.
     * 
     * @return the statement with the given index.
     * 
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of
     * bounds.
     */
    @Override
    public IABSStatement getStatementAt(int index) {
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public SourceElement getFirstElement() {
        if (isEmpty())
            return this;
        final SourceElement e = getBody().get(0);
        return (e instanceof ABSStatementBlock) ? e.getFirstElement() : e;
    }

    @Override
    public int getPrefixLength() {
        return prefixElementArray.size();
    }

    @Override
    public ProgramPrefix getPrefixElementAt(int i) {
        return prefixElementArray.get(i);
    }

    @Override
    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return prefixElementArray;
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        if (firstActiveChildPos == null) {
            firstActiveChildPos = isEmpty() ? PosInProgram.TOP
                    : PosInProgram.TOP.down(0);
        }
        return firstActiveChildPos;
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSStatementBlock(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("{\n");
        printBody(sb);
        return sb.append("}").toString();
    }

    protected void printBody(StringBuilder sb) {
        for (int i = 0; i < getStatementCount(); i++) {
            sb.append("\t").append(getStatementAt(i)).append("\n");
        }
    }

}
