//package de.uka.ilkd.key.loopinvgen;
//
//import java.util.ArrayList;
//import java.util.Arrays;
//import java.util.Iterator;
//import java.util.List;
//
//import org.apache.commons.math3.util.CombinatoricsUtils;
//import org.key_project.util.collection.ImmutableArray;
//
//
//import de.uka.ilkd.key.java.ProgramElement;
//import de.uka.ilkd.key.java.Services;
//import de.uka.ilkd.key.logic.Term;
//import de.uka.ilkd.key.logic.TermBuilder;
//import de.uka.ilkd.key.speclang.BlockSpecificationElement.Terms;
//
//public class ConjuctionConstruction {
//	
//	private final Services services;
//	private final ProgramElement root;
//	private final TermBuilder tb;
//	
//	private ArrayList<int[]> numericCombination = null;
//	
//	public ArrayList<Term> allTermCombinations = null;
//	
//	public ConjuctionConstruction(ProgramElement root, Services services) {
//		this.services = services;
//		this.root = root;
//		this.tb = services.getTermBuilder();
//	}
//	
//
//	
//	public void differentCombination(int n) {//n: number of cunstraucted predicates
//		for(int r=0; r<=n; r++) {
//			Iterator<int[]> iterator = CombinatoricsUtils.combinationsIterator(n, r);
//			while (iterator.hasNext()) {
//		        final int[] combination = iterator.next();
//		        System.out.println(Arrays.toString(combination));
//		        numericCombination.add(combination);
//		    }
//		}
//	}
//	
//	public Term conjuctionOfAll(ConstructAllPredicates cap) {// preds ha bishtar az in ha hastand. chon be ezaye har locset yeki darim. hame ra dar yek araye berizam.
//	Term t = tb.and(cap.noRPred, cap.noWPred, cap.noRaWPred, cap.noWaRPred, cap.noWaWPred);
//	return t;
//	}
//	
//	public Term combinationMap(int[] oneComb, Term[] preds) {
//		Term t = null;
//		for(int i = 0; i < oneComb.length; i++) {
//			t = tb.and(preds[oneComb[i]]);
//		}
//		return t;
//	}
//	
//	public void blah(ArrayList<int[]> numComb, Term[] preds) {
//		Term t = null;
//		for(int[] nc:numComb){
//			allTermCombinations.add(combinationMap(nc, preds));
//		}
//	}
//	
//	
//	
////	public static void generate(int n, int r) {
////	    Iterator<int[]> iterator = CombinatoricsUtils.combinationsIterator(n, r);
////	    while (iterator.hasNext()) {
////	        final int[] combination = iterator.next();
////	        System.out.println(Arrays.toString(combination));
////	    }
////	}
//
//}
