package de.uka.ilkd.key.gui.proofdiff;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;

import java.util.Iterator;

/**
 * Class that handles the diff of sequents
 * Created by sarah on 1/26/17.
 */
public class SequentDiff {
    Sequent seqBefore;
    Sequent seqAfter;

    public SequentDiff(Sequent sefBefore, Sequent seqAfter){
        this.seqBefore = sefBefore;
        this.seqAfter = seqAfter;
        init();
    }

    public void init(){
       // SequentChangeInfo
        Semisequent antecedentBefore = seqBefore.antecedent();
        Semisequent succedentBefore = seqBefore.succedent();


        Semisequent antecedentAfter = seqAfter.antecedent();
        Semisequent succedentAfter = seqAfter.succedent();

        if(antecedentAfter.size() == antecedentBefore.size()){
            System.out.println("Antecedent Sizes equal");
        }

        if(antecedentAfter.size() > antecedentBefore.size()){
            System.out.println("A formula was added");
            findAddedFormula(antecedentBefore, antecedentAfter);
        }
        if(succedentAfter.size() == succedentBefore.size()){
            System.out.println("Succedent Sizes equal");
        }
        if(succedentAfter.size() > succedentBefore.size()){
            System.out.println("A formula was added");
             findAddedFormula(succedentBefore, succedentAfter);
        }

    }


    /**
     * If the child's antcedent or succedent has more formula elements than  the parent, assume formulas were added
     * @param before
     * @param after
     */
    public void findAddedFormula(Semisequent before, Semisequent after){
        if(before.size() == 0){
            System.out.println("Diff found: "+after.toString());
        }else {
            Iterator<SequentFormula> beforeIter = before.iterator();
            Iterator<SequentFormula> afterIter = after.iterator();
            while (afterIter.hasNext()) {
                SequentFormula aft = afterIter.next();
                SequentFormula bef = beforeIter.next(); //null pointer
                if (!aft.equals(bef)) {
                    System.out.println("Diff found: " + aft.formula().toString() + bef.formula().toString());
                }
            }
        }

    }

    /**
     * If the child's antcedent or succedent has less formula elements than  the parent, assume formulas were deleted or moved
     * @param before
     * @param after
     */
    public void findDeletedFormula(Semisequent before, Semisequent after){


    }

}
