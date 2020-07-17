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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import de.uka.ilkd.key.proof.Proof;

public class ProofResult {
    public static final ProofResult EMPTY = new ProofResult(true, Collections.emptyList());
    public static final Collector<ProofResult, ?, ProofResult> REDUCER = Collectors.reducing(EMPTY,
            (r1, r2) -> r1.merge(r2));

    private final boolean success;
    private final List<Proof> proofs;

    public ProofResult(boolean success, Proof proof) {
        this.success = success;
        this.proofs = new ArrayList<>();
        this.proofs.add(proof);
    }

    public ProofResult(boolean success, List<Proof> proofs) {
        this.success = success;
        this.proofs = proofs;
    }

    public Proof getProof() {
        return proofs.get(0);
    }

    public List<Proof> getProofs() {
        return proofs;
    }

    public ProofResult merge(ProofResult other) {
        final boolean success = this.success && other.success;
        final List<Proof> proofs = new ArrayList<>();
        proofs.addAll(this.proofs);
        proofs.addAll(other.proofs);
        return new ProofResult(success, proofs);
    }

    public boolean isSuccess() {
        return success;
    }
}