package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/*
 * Provides the possible MessageTypes in component based systems, i.e. call and termination
 */
public class MessageTypeValue extends AbstractOperator {
    
    /** 
     * the CALL constant 
     */
    public static final MessageTypeValue CALL = new MessageTypeValue(new Name("call"));

    /** 
     * the false constant 
     */
    public static final MessageTypeValue TERMINATION = new MessageTypeValue(new Name("termination"));

    private MessageTypeValue(Name name) {
        super(name, 0, true);
    }

    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        return Sort.MESSAGETYPE;
    }

    @Override
    protected boolean additionalValidTopLevel(Term term) {
        // TODO allows anything, restrict this? Find out what this does exactly...
        return true;
    }

}
