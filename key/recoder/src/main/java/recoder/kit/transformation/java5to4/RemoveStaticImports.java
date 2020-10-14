/*
 * Created on 25.03.2006
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Import;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.NameReference;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.UnitKit;

/**
 * Removes static imports from a given Compilation Unit and adds 
 * qualfication prefixes to (possible) uses of such imports.
 * 
 * @author Tobias Gutzmann
 * @since 0.80
 *
 */
public class RemoveStaticImports extends TwoPassTransformation {
	private List<CompilationUnit> cul;
	
	private static class Item {
		NameReference r;
		TypeReference prefix;
		Item(NameReference r, TypeReference prefix) {
			this.r = r;
			this.prefix = prefix;
		}
	}
	
	private List<Item> hotSpots;
	
	private List<Import> statics;
	
	/**
	 * @param sc
	 */
	public RemoveStaticImports(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
		super(sc);
		cul = new ArrayList<CompilationUnit>();
		cul.add(cu);
	}
	
	public RemoveStaticImports(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
	}

	@Override
	public ProblemReport analyze() {
		hotSpots = new ArrayList<Item>();
		statics = new ArrayList<Import>();
		// are there any static imports at all?
		for (CompilationUnit cu : cul) {
			List<Import> il = cu.getImports();
			if (il == null || il.isEmpty())
				continue;
			for (int i = 0, s = il.size(); i < s; i++) {
				Import im = il.get(i);
				if (im.isStaticImport())
					statics.add(im);
			}
			if (statics.isEmpty())
				continue;
			
			// traverse tree, consider member references only
			TreeWalker tw = new TreeWalker(cu);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				if (pe instanceof MemberReference && pe instanceof ReferenceSuffix && pe instanceof NameReference) {
					MemberReference r = (MemberReference)pe;
					ReferenceSuffix s = (ReferenceSuffix)pe;
					NameReference nr = (NameReference)pe;
					if (s.getReferencePrefix() != null) 
						continue; // not found through a static import
					ClassType targetCT;
					if (r instanceof MethodReference) {
						targetCT = getSourceInfo().getMethod((MethodReference)r).getContainingClassType();
					} else if (r instanceof FieldReference) {
						targetCT = getSourceInfo().getField((FieldReference)r).getContainingClassType();
					} else if (r instanceof TypeReference) {
						Type t = getSourceInfo().getType((TypeReference)r);
						if (!(t instanceof ClassType))
							continue;
						targetCT = (ClassType)t;
					} else {
						continue;
					}
					if (targetCT instanceof TypeDeclaration && UnitKit.getCompilationUnit((TypeDeclaration)targetCT) == cu)
						continue;
					String n = nr.getName();
					for (int i = 0, si = statics.size(); i < si; i++) {
						Import im = statics.get(i);
						TypeReference tr = im.getTypeReference(); // has to be set!
//						System.out.println(tr.getName());
						if ((ClassType)getSourceInfo().getType(tr) != targetCT)
							continue;
						if (im.isMultiImport()) {
							// TODO may still not be it... unlikely, but yet...
							// (different type import may match)
							// however, the way we currently handle this, no harm is done...
						} else {
							if (!n.equals(im.getStaticIdentifier().getText()))
								continue;
							// TODO check: if another import matches, I *think*
							// that should be a semantic error
							// however, the way we currently handle this, no harm is done...
						}
						TypeReference prefix = im.getTypeReference();
						hotSpots.add(new Item(nr,prefix));
						break;
					}
				}
			}
		}
		return super.analyze();
	}

	private boolean isChild(NonTerminalProgramElement nr1, NameReference nr2) {
		NameReference tmp;
		for (int c = 0; c < nr1.getChildCount(); c++) {
			if (nr1.getChildAt(c) instanceof NameReference) {
				tmp = (NameReference)nr1.getChildAt(c);
				if (tmp.equals(nr2)) return true;
				else return isChild(tmp, nr2);
			}
			else if(nr1.getChildAt(c) instanceof NonTerminalProgramElement)
				return isChild((NonTerminalProgramElement)nr1.getChildAt(c),nr2);
		}
		return false;
	}
	
	private void sortReferences(List<Item> its) {
		boolean changed = true;
		Item it1,it2,tmp;
		while (changed) {
			changed = false;
			for (int i = 0; i < its.size() - 1; i++) {
				for (int j = i + 1; j < its.size(); j++) {
					it1 = its.get(i);
					it2 = its.get(j);
					if (isChild(it1.r,it2.r)) {
						tmp = its.get(i);
						its.set(i, it2);
						its.set(j, tmp);
						changed = true;
//						System.out.println("changed");
					}
				}
			}
		}
	}
	
	@Override
	public void transform() {
		super.transform();
		sortReferences(hotSpots);
		System.out.println("static imports: " + statics.size() + " hotSpots: " + hotSpots.size());
		for (Import i : statics) {
			detach(i);
		}
		for (Item hs : hotSpots) {
			String x = Naming.toPathName(hs.prefix, hs.r.getName());
			if (x.startsWith("java.lang."))
				x = x.substring(10);
			
			if (hs.r instanceof MethodReference) {
				MethodReference old = (MethodReference)hs.r;
				int i = x.lastIndexOf('.');
				x = x.substring(0,i);
				UncollatedReferenceQualifier urq = MiscKit.createUncollatedReferenceQualifier(getProgramFactory(), x);
				MethodReference mr = new MethodReference(urq, old.getIdentifier(), old.getArguments(), old.getTypeArguments());
				replace(old, mr);
			}
			else {
				UncollatedReferenceQualifier urq = MiscKit.createUncollatedReferenceQualifier(getProgramFactory(), x);
				replace(hs.r, urq);
			}
		}
	}
}
