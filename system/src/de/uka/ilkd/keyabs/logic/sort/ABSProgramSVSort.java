package de.uka.ilkd.keyabs.logic.sort;

import java.util.HashMap;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.IProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.sort.programSV.*;

public abstract class ABSProgramSVSort extends AbstractSort implements IProgramSVSort<ABSServices> {

    // Keeps the mapping of ProgramSVSort names to
    // ProgramSVSort instances (helpful in parsing
    // schema variable declarations)
    private static final HashMap<Name, IProgramSVSort<ABSServices>> name2sort =
        new HashMap<Name, IProgramSVSort<ABSServices>>(60);
  
    public static HashMap<Name, IProgramSVSort<ABSServices>> name2sort() {
        return name2sort;
    }

    public static final IProgramSVSort<ABSServices> ABS_PUREEXPRESSION = new ABSPureExpSV();
    public static final IProgramSVSort<ABSServices> ABS_VARIABLE = new ABSVariableSV();
    public static final IProgramSVSort<ABSServices> ABS_FIELD = new ABSFieldSV();
    public static final IProgramSVSort<ABSServices> ABS_METHODLABEL = new ABSMethodLabelSV();
    public static final IProgramSVSort<ABSServices> ABS_STATEMENT = new ABSStatementSV();
    public static final IProgramSVSort<ABSServices> ABS_TYPEREF = new ABSTypeReferenceSV();
    public static final IProgramSVSort<ABSServices> ABS_INTERFACE_TYPEREF = new ABSInterfaceTypeReferenceSV();
    public static final IProgramSVSort<ABSServices> ABS_METHODNAME = new ABSMethodNameSV();
    
    
    public ABSProgramSVSort(Name name) {
        super(name, DefaultImmutableSet.<Sort>nil(), false);
        name2sort.put(name, this);
    }

    @Override
    public boolean canStandFor(Term t) {
        return true;
    }

    @Override
    public abstract boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services);

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.sort.IProgramSVSort#createInstance(java.lang.String)
     */
    @Override
    public IProgramSVSort<ABSServices> createInstance(String parameter) {
      throw new UnsupportedOperationException();
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.sort.IProgramSVSort#getSVWithSort(de.uka.ilkd.key.util.ExtList, java.lang.Class)
     */
    @Override
    public ProgramElement getSVWithSort(ExtList l, Class alternative) {
        for (final Object o : l) {
            if (o instanceof SchemaVariable
                && (((SchemaVariable)o).sort()==this)) {
                return (ProgramElement) o;
            } else if ((alternative.isInstance(o))
                    && (!(o instanceof SchemaVariable))) {
                return (ProgramElement) o;
            }
        }
        return null;
    }

}
