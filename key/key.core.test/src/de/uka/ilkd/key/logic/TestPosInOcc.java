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

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.LogicVariable;
import org.key_project.common.core.logic.sort.Sort;

import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;


public class TestPosInOcc extends TestCase {
    
    private static TermBuilder TB;

    public TestPosInOcc(String name) {
	super(name);
    }

    @Override
    public void setUp () {
       TB = TacletForTests.services().getTermBuilder();
    }
    
    public void testIterator () {
	Sort sort1=new SortImpl(new Name("S1"));
	LogicVariable x=new LogicVariable(new Name("x"),sort1);  
	Function f=new Function(new Name("f"),sort1,new Sort[]{sort1});
	Function p=new Function(new Name("p"),Sort.FORMULA,new Sort[]{sort1});

	
	JavaDLTerm terms[] = new JavaDLTerm [ 3 ];
	terms[0]     = TB.var ( x );
	terms[1]     = TB.func ( f, new JavaDLTerm[] { terms[0] } );
	terms[2]     = TB.func ( p, new JavaDLTerm[] { terms[1] } );

	PosInOccurrence pio = new PosInOccurrence
	    ( new SequentFormula ( terms[2] ),
	      PosInTerm.getTopLevel(),
	    true);

	PIOPathIterator it = pio.iterator ();

	// a top-level position

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == -1 );

	// two nodes deeper

	pio = pio.down ( 0 ).down ( 0 );
	it = pio.iterator ();

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[2] &&
		     it.getPosInOccurrence ().subTerm () == terms[2] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == 0 &&
		     it.getSubTerm () == terms[1] &&
		     it.getPosInOccurrence ().subTerm () == terms[1] &&
		     it.getChild () == 0 );

	assertTrue ( it.hasNext () );
	assertTrue ( it.next () == -1 &&
		     it.getSubTerm () == terms[0] &&
		     it.getPosInOccurrence ().subTerm () == terms[0] &&
		     it.getChild () == -1 );

	assertFalse ( it.hasNext () );
    }

    
    public void testReplaceConstrainedFormula () {
        Sort sort1 = new SortImpl ( new Name ( "S1" ) );
        LogicVariable x = new LogicVariable ( new Name ( "x" ), sort1 );        
        Function c = new Function ( new Name ( "c" ), sort1, new Sort[] {} );
        Function f = new Function ( new Name ( "f" ),
                                    sort1,
                                    new Sort[] { sort1 } );
        Function p = new Function ( new Name ( "p" ),
                                    Sort.FORMULA,
                                    new Sort[] { sort1 } );

        JavaDLTerm terms[] = new JavaDLTerm[3];
        terms[0] = TB.var( x );
        terms[1] = TB.func ( f, new JavaDLTerm[] { terms[0] } );
        terms[2] = TB.func ( p, new JavaDLTerm[] { terms[1] } );
        SequentFormula cfma = new SequentFormula ( terms[2] );

        JavaDLTerm terms2[] = new JavaDLTerm[4];
        terms2[0] = TB.func ( c );
        terms2[1] = TB.func ( f, new JavaDLTerm[] { terms2[0] } );
        terms2[2] = TB.func ( f, new JavaDLTerm[] { terms2[1] } );
        terms2[3] = TB.func ( p, new JavaDLTerm[] { terms2[2] } );
        SequentFormula cfma2 = new SequentFormula ( terms2[3] );

        final PosInOccurrence topPIO = new PosInOccurrence ( cfma,
                                                             PosInTerm.getTopLevel(),
                                                             true );


        // Test without metavariables involved
        PosInOccurrence pio = topPIO.down ( 0 );
        assertTrue ( pio.subTerm () == terms[1] );
        PosInOccurrence pio2 = pio.replaceConstrainedFormula ( cfma );
        assertEquals ( pio, pio2 );
        pio = pio.replaceConstrainedFormula ( cfma2 );
        assertTrue ( pio.subTerm () == terms2[2] );
    }
}