// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import org.key_project.common.core.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class InfFlowBlockContractTacletBuilder
        extends AbstractInfFlowContractAppTacletBuilder {

    private BlockContract blockContract;
    private ExecutionContext executionContext;


    public InfFlowBlockContractTacletBuilder(final Services services) {
        super(services);
    }


    public void setContract(BlockContract contract) {
        this.blockContract = contract;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    @Override
    Name generateName() {
        return MiscTools.toValidTacletName(USE_IF + blockContract.getUniqueName());
    }

    @Override
    JavaDLTerm generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                               Services services) {
        BasicPOSnippetFactory fAssumes =
                POSnippetFactory.getBasicFactory(blockContract, schemaDataAssumes,
                                                 executionContext, services);
        return fAssumes.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    JavaDLTerm generateSchemaFind(ProofObligationVars schemaDataFind,
                            Services services) {
        BasicPOSnippetFactory fFind =
                POSnippetFactory.getBasicFactory(blockContract, schemaDataFind,
                                                 executionContext, services);
        return fFind.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    JavaDLTerm getContractApplPred(ProofObligationVars appData) {
        BasicPOSnippetFactory f =
                POSnippetFactory.getBasicFactory(blockContract, appData,
                                                 executionContext, services);
        return f.create(BasicPOSnippetFactory.Snippet.BLOCK_CALL_RELATION);
    }


    @Override
    JavaDLTerm buildContractApplications(ProofObligationVars contAppData,
                                   ProofObligationVars contAppData2,
                                   Services services) {
        ImmutableSet<BlockContract> ifContracts =
                services.getSpecificationRepository().getBlockContracts(blockContract.getBlock());
        ifContracts = filterContracts(ifContracts);
        ImmutableList<JavaDLTerm> contractsApplications = ImmutableSLList.<JavaDLTerm>nil();
        for (BlockContract cont : ifContracts) {
            InfFlowPOSnippetFactory f =
                    POSnippetFactory.getInfFlowFactory(cont, contAppData,
                                                       contAppData2,
                                                       executionContext,
                                                       services);
            contractsApplications =
                    contractsApplications.append(
                    f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL));
        }

        return and(contractsApplications);
    }


    ImmutableSet<BlockContract> filterContracts(ImmutableSet<BlockContract> ifContracts) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.<BlockContract>nil();
        for (BlockContract cont : ifContracts) {
            if ((cont.getBlock().getStartPosition().getLine() ==
                    blockContract.getBlock().getStartPosition().getLine()) &&
                    cont.getTarget().getUniqueName()
                    .equalsIgnoreCase(blockContract.getTarget().getUniqueName())) {
                result = result.add(cont);
            }
        }
        return result;
    }
}