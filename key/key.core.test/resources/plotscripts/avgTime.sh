#!/usr/bin/gnuplot

set term pngcairo # antialiasing: http://stackoverflow.com/questions/9080832/output-png-from-gnuplot-is-not-as-good-as-the-figure-from-prompt-shell
set output 'avgTime.png'

set xlabel "Length of formula (AST grows linearly for generated formulas)"
set ylabel "Average time for a single computeCost() invocation"

set title "computeCost() statistics" # the title printed above the graph
set key below # print curve titles below graph
set grid # adds dotted grid lines to the output graph

plot "data.csv" using 1:3 with lines title "lines",\
     "data.csv" using 1:3 with lines title "csplines" smooth csplines,\
     "data.csv" using 1:3 with lines title "bezier" smooth bezier

