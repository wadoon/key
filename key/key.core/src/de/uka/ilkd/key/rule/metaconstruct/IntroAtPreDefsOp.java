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

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.*;

import org.key_project.common.core.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

public final class IntroAtPreDefsOp extends AbstractTermTransformer {

    private static final Comparator<LocationVariable> LOCVAR_COMPARATOR =
            new Comparator<LocationVariable>() {
        @Override
        public int compare(LocationVariable o1, LocationVariable o2) {
            return o1.name().compareTo(o2.name());
        }
    };


    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }


    @Override
    public JavaDLTerm transform(JavaDLTerm term,
                  SVInstantiations svInst,
                  Services services) {
        final TermBuilder TB = services.getTermBuilder();
        final JavaDLTerm target = term.sub(0);

        //the target term should have a Java block
        final ProgramElement pe = target.modalContent().program();
        assert pe != null;

        //collect all loops in the innermost method frame
        final Triple<MethodFrame,
                     ImmutableSet<LoopStatement>,
                     ImmutableSet<StatementBlock>> frameAndLoopsAndBlocks =
              new JavaASTVisitor(pe, services) {
            private MethodFrame frame = null;
            private ImmutableSet<LoopStatement> loops
                = DefaultImmutableSet.<LoopStatement>nil();
            private ImmutableSet<StatementBlock> blocks
                = DefaultImmutableSet.nil();
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && frame == null) {
                    frame = (MethodFrame) node;
                } else if(frame == null && node instanceof LoopStatement) {
                    loops = loops.add((LoopStatement) node);
                }
                else if (frame == null && node instanceof StatementBlock) {
                    blocks = blocks.add((StatementBlock) node);
                }
            }
            public Triple<MethodFrame,
                          ImmutableSet<LoopStatement>,
                          ImmutableSet<StatementBlock>> run() {
                walk(root());
                return new Triple<MethodFrame,
                                  ImmutableSet<LoopStatement>,
                                  ImmutableSet<StatementBlock>>(
                        frame, loops, blocks);
            }
        }.run();
        final MethodFrame frame = frameAndLoopsAndBlocks.first;
        final ImmutableSet<LoopStatement> loops = frameAndLoopsAndBlocks.second;

        //determine "self"
        JavaDLTerm selfTerm;
        final ExecutionContext ec
            = (ExecutionContext) frame.getExecutionContext();
        final ReferencePrefix rp = ec.getRuntimeInstance();
        if(rp == null || rp instanceof TypeReference) {
            selfTerm = null;
        } else {
            selfTerm = services.getProgramServices().getTypeConverter().convertToLogicElement(rp);
        }

        //create atPre heap
        final String methodName = frame.getProgramMethod().getName();

        JavaDLTerm atPreUpdate = null;
        Map<LocationVariable,JavaDLTerm> atPres = new LinkedHashMap<LocationVariable,JavaDLTerm>();
        Map<LocationVariable,LocationVariable> atPreVars = new LinkedHashMap<LocationVariable, LocationVariable>();
        for(LocationVariable heap : services.getTheories().getHeapLDT().getAllHeaps()) {
          final LocationVariable l = TB.heapAtPreVar(heap.name()+"Before_" + methodName, heap.sort(), true);
          // buf fix. see #1197
          services.getNamespaces().programVariables().addSafely(l);
          final JavaDLTerm u = TB.elementary(l, TB.var(heap));
          if(atPreUpdate == null) {
             atPreUpdate = u;
          }else{
             atPreUpdate = TB.parallel(atPreUpdate, u);
          }
          atPres.put(heap, TB.var(l));
          atPreVars.put(heap, l);
        }

        //create atPre for parameters
        for (LoopStatement loop : loops) {
            LoopInvariant inv
               = services.getSpecificationRepository().getLoopInvariant(loop);
            if(inv != null) {
                // Nasty bug! The order of these things was not constant! Would fail indeterministically
                // when reloading. Better sort the variables.
                List<LocationVariable> keys = new ArrayList<LocationVariable>(inv.getInternalAtPres().keySet());
                Collections.sort(keys, LOCVAR_COMPARATOR);
                for (LocationVariable var : keys) {
                    if(atPres.containsKey(var)) {
                        // heaps have already been considered, or more than one loop
                        continue;
                    }
                    final LocationVariable l = TB.heapAtPreVar(var.name()+"Before_" + methodName, var.sort(), true);
                    services.getNamespaces().programVariables().addSafely(l);
                    final JavaDLTerm u = TB.elementary(l, TB.var(var));
                    if(atPreUpdate == null) {
                        atPreUpdate = u;
                    } else {
                        atPreUpdate = TB.parallel(atPreUpdate, u);
                    }
                    atPres.put(var, TB.var(l));
                    atPreVars.put(var, l);
                }
            }
        }

        //update loop invariants
        for(LoopStatement loop : loops) {
            LoopInvariant inv
                = services.getSpecificationRepository().getLoopInvariant(loop);
            if(inv != null) {
                if(selfTerm != null && inv.getInternalSelfTerm() == null) {
                    //we're calling a static method from an instance context
                    selfTerm = null;
                }

                final JavaDLTerm newVariant
                    = inv.getVariant(selfTerm, atPres, services);

                Map<LocationVariable,JavaDLTerm> newMods = new LinkedHashMap<LocationVariable,JavaDLTerm>();
                Map<LocationVariable,
                    ImmutableList<InfFlowSpec>> newInfFlowSpecs
                                 = new LinkedHashMap<LocationVariable,
                                                     ImmutableList<InfFlowSpec>>();
                //LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
                Map<LocationVariable,JavaDLTerm> newInvariants = new LinkedHashMap<LocationVariable,JavaDLTerm>();
                for(LocationVariable heap : services.getTheories().getHeapLDT().getAllHeaps()) {
                  if(heap == services.getTheories().getHeapLDT().getSavedHeap()
                     &&
                     inv.getInternalModifies().get(services.getTheories().getHeapLDT().getHeap()).equals(TB.strictlyNothing())) {
                    continue;
                  }
                  final JavaDLTerm m = inv.getModifies(heap, selfTerm, atPres, services);
                  final ImmutableList<InfFlowSpec> infFlowSpecs =
                                 inv.getInfFlowSpecs(heap, selfTerm, atPres, services);
                  final JavaDLTerm in = inv.getInvariant(heap, selfTerm, atPres, services);
                  if(m != null) { newMods.put(heap, m); }
                  newInfFlowSpecs.put(heap, infFlowSpecs);
                  if(in != null) { newInvariants.put(heap, in); }
                }
                ImmutableList<JavaDLTerm> newLocalIns = TB.var(MiscTools.getLocalIns(loop, services));
                ImmutableList<JavaDLTerm> newLocalOuts = TB.var(MiscTools.getLocalOuts(loop, services));
                final LoopInvariant newInv
                       = inv.create(loop,
                                    frame.getProgramMethod(),
                                    frame.getProgramMethod().getContainerType(),
                                    newInvariants,
                                    newMods,
                                    newInfFlowSpecs,
                                    newVariant,
                                    selfTerm,
                                    newLocalIns,
                                    newLocalOuts,
                                    atPres);
                services.getSpecificationRepository().addLoopInvariant(newInv);
            }
        }

        /*//update block contracts
        for (StatementBlock block : blocks) {
            ImmutableSet<BlockContract> contracts =
                    services.getSpecificationRepository().getBlockContracts(block);
            for (BlockContract contract : contracts) {
                final BlockContract.Variables variables = contract.getPlaceholderVariables();
                final BlockContract.Variables newVariables = new BlockContract.Variables(
                        variables.self,
                        variables.breakFlags,
                        variables.continueFlags,
                        variables.returnFlag,
                        variables.result,
                        variables.exception,
                        atPreVars,
                        variables.remembranceLocalVariables
                );
                final Map<LocationVariable, JavaDLTerm> newPreconditions =
                        new LinkedHashMap<LocationVariable, JavaDLTerm>();
                final Map<LocationVariable, JavaDLTerm> newPostconditions =
                        new LinkedHashMap<LocationVariable, JavaDLTerm>();
                final Map<LocationVariable, JavaDLTerm> newModifiesClauses =
                        new LinkedHashMap<LocationVariable, JavaDLTerm>();
                ImmutableList<Triple<ImmutableList<JavaDLTerm>,
                                     ImmutableList<JavaDLTerm>,
                                     ImmutableList<JavaDLTerm>>> newRespectsClause =
                        ImmutableSLList.<Triple<ImmutableList<JavaDLTerm>,
                                                ImmutableList<JavaDLTerm>,
                                                ImmutableList<JavaDLTerm>>>nil();
                for (LocationVariable heap : HeapContext.getModHeaps(services, transaction)) {
                    newPreconditions.put(heap,
                                         contract.getPrecondition(heap, newVariables.self,
                                                                  atPreVars, services));
                    newPostconditions.put(heap,
                                          contract.getPostcondition(heap, newVariables, services));
                    newModifiesClauses.put(heap,
                                           contract.getModifiesClause(heap, newVariables.self,
                                                                      services));
                    newRespectsClause = contract.getRespectsClause(newVariables.self,
                                                                   services);
                }
                final BlockContract newBlockContract =
                        contract.update(block, newPreconditions, newPostconditions,
                                        newModifiesClauses, newRespectsClause, newVariables);
                services.getSpecificationRepository().addBlockContract(newBlockContract);
            }
        }*/

        return TB.apply(atPreUpdate, target, null);
    }
}
