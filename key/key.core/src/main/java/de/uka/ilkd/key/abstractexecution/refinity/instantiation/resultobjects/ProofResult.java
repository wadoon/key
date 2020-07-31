// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofBundleSaver;
import de.uka.ilkd.key.util.Pair;

public class ProofResult implements Iterable<Pair<String, Proof>> {
    public static final ProofResult EMPTY = //
            new ProofResult(true, Collections.emptyList(), Collections.emptyList());
    public static final Collector<ProofResult, ?, ProofResult> REDUCER = //
            Collectors.reducing(EMPTY, (r1, r2) -> r1.merge(r2));

    private final boolean success;
    private final List<Proof> proofs;
    private final List<String> names;

    public ProofResult(boolean success, Proof proof, String name) {
        this.success = success;

        this.proofs = new ArrayList<>();
        this.names = new ArrayList<>();

        this.proofs.add(proof);
        this.names.add(name);
    }

    public ProofResult(boolean success, List<Proof> proofs, List<String> names) {
        assert proofs.size() == names.size();

        this.success = success;
        this.proofs = proofs;
        this.names = names;
    }

    public Proof getProof() {
        return proofs.get(0);
    }

    public String getName() {
        return names.get(0);
    }

    public List<Proof> getProofs() {
        return proofs;
    }

    public List<String> getNames() {
        return names;
    }

    public ProofResult merge(ProofResult other) {
        final boolean success = this.success && other.success;
        
        final List<Proof> proofs = new ArrayList<>();
        final List<String> names = new ArrayList<>();
        
        proofs.addAll(this.proofs);
        proofs.addAll(other.proofs);
        
        names.addAll(this.names);
        names.addAll(other.names);
        
        return new ProofResult(success, proofs, names);
    }

    public boolean isSuccess() {
        return success;
    }

    @Override
    public java.util.Iterator<Pair<String, Proof>> iterator() {
        return new java.util.Iterator<Pair<String, Proof>>() {
            int idx = -1;

            @Override
            public Pair<String, Proof> next() {
                idx++;
                return new Pair<String, Proof>(getNames().get(idx), getProofs().get(idx));
            }

            @Override
            public boolean hasNext() {
                return idx + 1 < getProofs().size();
            }
        };
    }

    public boolean saveBundlesToDir(final Path outputDir) throws IOException {
        if (!outputDir.toFile().exists()) {
            if (!outputDir.toFile().mkdirs()) {
                return false;
            }
        }

        for (Pair<String, Proof> proofAndName : this) {
            final Proof proof = proofAndName.second;
            final String name = proofAndName.first;

            final ProofBundleSaver saver = new ProofBundleSaver(proof,
                    outputDir.resolve(name).toFile());
            
            saver.save();
        }

        return true;
    }
}