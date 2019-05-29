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

package de.uka.ilkd.key.rule;

import java.util.Optional;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** 
 * Simple container class containing the information resulting from a
 * Taclet.match-call 
 */
public class MatchConditions {

    public static final MatchConditions EMPTY_MATCHCONDITIONS =
	new MatchConditions ( SVInstantiations.EMPTY_SVINSTANTIATIONS,
			      RenameTable.EMPTY_TABLE, Optional.empty());

    private final SVInstantiations instantiations;
    private final RenameTable renameTable;

    /**
     * The {@link SequentFormula} of the subterm where we currently check the
     * {@link MatchCondition}. This is for cases where we need more context
     * information. Was introduced for Abstract Execution: For the choice of the
     * "right" contract, we there need the variables of the surroundings. Maybe
     * there's another way to deal with renamings and arising multiple
     * contracts, then this can be removed again (DS, 2019-01-30).
     */
    private final Optional<SequentFormula> maybeSeqFor;
    public MatchConditions() {
        this.instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        this.renameTable = RenameTable.EMPTY_TABLE;
        this.maybeSeqFor = Optional.empty();
    }
    
    public MatchConditions ( SVInstantiations   p_instantiations,
			     RenameTable        p_renameTable, Optional<SequentFormula> maybeSeqFor) {
        assert p_instantiations != null;
        assert p_renameTable != null;
        instantiations   = p_instantiations;	
        renameTable      = p_renameTable; 
        this.maybeSeqFor = maybeSeqFor;
    }

    public SVInstantiations   getInstantiations   () {
	return instantiations;
    }

    public Optional<SequentFormula> getMaybeSeqFor() {
        return maybeSeqFor;
    }

    public MatchConditions    setInstantiations   ( SVInstantiations   p_instantiations ) {
	if ( instantiations == p_instantiations )
	    return this;
	else
	    return new MatchConditions ( p_instantiations, 
                                         renameTable, maybeSeqFor);
    }

    public MatchConditions setSeqFor(PosInOccurrence pio) {
        return new MatchConditions(this.instantiations, this.renameTable,
                Optional.ofNullable(pio).map(PosInOccurrence::sequentFormula));
    }

    public MatchConditions setSeqFor(SequentFormula seqFor) {
        return new MatchConditions(this.instantiations, this.renameTable,
                Optional.of(seqFor));
    }
    
    public MatchConditions extendRenameTable() {        
        return new MatchConditions(instantiations, renameTable.extend(), maybeSeqFor);
    }    

    public MatchConditions addRenaming(QuantifiableVariable q1, QuantifiableVariable q2) {        
        return new MatchConditions(instantiations, renameTable.assign(q1, q2), maybeSeqFor);
    }    
    
    public RenameTable renameTable() {
        return renameTable;
    }

    public MatchConditions shrinkRenameTable() {      
        return new MatchConditions(instantiations, renameTable.parent(), maybeSeqFor);
    }

    
}
