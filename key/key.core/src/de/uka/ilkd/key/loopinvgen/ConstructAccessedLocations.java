//package de.uka.ilkd.key.loopinvgen;
//
//import org.key_project.util.collection.DefaultImmutableSet;
//import org.key_project.util.collection.ImmutableArray;
//import org.key_project.util.collection.ImmutableSet;
//
//import de.uka.ilkd.key.java.NonTerminalProgramElement;
//import de.uka.ilkd.key.java.ProgramElement;
//import de.uka.ilkd.key.java.Reference;
//import de.uka.ilkd.key.java.Services;
//import de.uka.ilkd.key.java.expression.Assignment;
//import de.uka.ilkd.key.java.reference.ThisReference;
//import de.uka.ilkd.key.logic.Term;
//
//public class ConstructAccessedLocations {
//
//	// TODO: what should I do for a range in an array??
//	
//	private ImmutableSet<Reference> rLocs = DefaultImmutableSet.<Reference>nil();
//	private ImmutableSet<Reference> wLocs = DefaultImmutableSet.<Reference>nil();
//	
//	public ImmutableArray<Term> rArr = null;
//	public ImmutableArray<Term> wArr = null;
//	public ImmutableArray<Term> rUnionWArr = null;
//	public ImmutableArray<Term> rIntersectWArr = null;
//	public ImmutableArray<Term> rMinusWArr = null;
//	public ImmutableArray<Term> wMinusRArr = null;
//
//	
//	public ConstructAccessedLocations(ProgramElement body, Services services) {
//
//	}
//
//	public void collectReadAndWrittenPVs(ProgramElement body) {
//		if (body instanceof NonTerminalProgramElement) {
////			System.out.println("NonTerminalProgramElement: " + node);
//			NonTerminalProgramElement nonTerminalNode = (NonTerminalProgramElement) body;
//			if (nonTerminalNode instanceof Assignment) {
////				System.out.println("Assignment: " + nonTerminalNode);
//				ProgramElement lhs = ((Assignment) nonTerminalNode).getChildAt(0);
////				System.out.println("Left of assignment " + lhs);
//				if (lhs instanceof Reference) { //FieldReference or ArrayReference
////					System.out.println("Left Program Variable: " + lhs);
//					if (!this.wLocs.contains((Reference) lhs)) {
////						System.out.println("Written program variable: " + lhs);
//						this.wLocs = this.wLocs.add((Reference) lhs);
//					}
//				}
//				if (((Assignment) nonTerminalNode).getChildCount() > 1) {//nabayad faghat tarafe raste assinment ra berizam. chom
//					ProgramElement rhs = ((Assignment) nonTerminalNode).getChildAt(1);
////					System.out.println("Right of assignment " + rhs);
//					if (rhs instanceof Reference) {
////						System.out.println("Right Program Variable: " + rhs);
//						if (!this.rLocs.contains((Reference) rhs)) {
////							System.out.println("Read program variable: " + rhs);
//							this.rLocs = this.rLocs.add((Reference) rhs);
//						}
//					}
//				}
//			}
//			for (int i = 0; i < nonTerminalNode.getChildCount(); i++) {
//				if (nonTerminalNode.getChildAt(i) != null
//						&& !(nonTerminalNode.getChildAt(i) instanceof ThisReference)) {
//					collectReadAndWrittenPVs(nonTerminalNode.getChildAt(i));
//				}
//			}
//		}
//	}
//
//	
//	
//	public ImmutableSet<Reference> setMinus(ImmutableSet<Reference> setA, ImmutableSet<Reference> setB) {
//		ImmutableSet<Reference> tmp = setA;
//		for (Reference ref : setB)
//			if (tmp.contains(ref))
//				tmp = tmp.remove(ref);
//		return tmp;
//	}
//
//	public ImmutableArray<Term> toTermImmutableArray(ImmutableSet<Reference> locs){
//		Reference[] arr = new Reference[locs.size()];
//		locs.toArray(arr);
//		ImmutableArray<Reference> refArray = new ImmutableArray<Reference>(arr);
//		ImmutableArray<Term> termArray = new ImmutableArray<Term>((Term)refArray);
//		System.out.println("Term Array: " + termArray);
//		return termArray;
//	}
//	
//	public void mainFunc() {
//		this.rArr = this.toTermImmutableArray(rLocs);
//		this.wArr = this.toTermImmutableArray(wLocs);
//		this.rUnionWArr = this.toTermImmutableArray(this.rLocs.union(wLocs));
//		this.rIntersectWArr = this.toTermImmutableArray(this.rLocs.intersect(wLocs));
//		this.rMinusWArr = this.toTermImmutableArray(this.setMinus(rLocs, wLocs));
//		this.wMinusRArr = this.toTermImmutableArray(this.setMinus(wLocs, rLocs));
//
//	}
//}
