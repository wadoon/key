parser grammar KeYCommonParser;

@header {
    package org.key_project.common.core.parser;
}

options {
    tokenVocab = KeYCommonLexer;
}

init: ID*? ;
