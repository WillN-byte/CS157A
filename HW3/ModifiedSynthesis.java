/*
Algorithm3.26: Synthesis of Third-Normal-Form Relations W ith a Lossless Join and Dependency Preservation.

INPUT: A relation R and a set F of functional dependencies that hold for R.

OUTPUT: A decomposition of R into a collection of relations, each of which is
in 3NF. The decomposition has the lossless-join and dependency-preservation
properties.

METHOD: Perform the following steps:
1. Find a minimal basis for F, say G.
2. Partition the the functional dependencies in G according to their left hand sides (so two dependencies X→A and X→B with the same left hand sides will be in the same partition). Merge each partition into a single FD using the combining rule (so X→A and X→B would become X→AB). For each rule X→Y that results from merging the rules of a partition, use XY as the schema of one of the relations in the decomposition. 
3. If none of the relation schemas from Step 2 is a superkey for R, add
another relation whose schema is a key for R.
4. If the set of the attributes of one table in the decomposition is a subset of the attributes of a different output table it should be deleted from the decomposition.
*/

package HW3;

import java.util.Arrays;
import java.util.HashSet;
import java.util.ArrayList;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ModifiedSynthesis {

    // an array containing left hand side
    // and right hand side of a functional dependency
    static String[] items;
    // an array of string elements in left hand side
    static String[] lhs;
    // an array of string elements in right hand side
    static String[] rhs;

    // iArrayList of sets of numbers for left hand sides
    // ArrayList of sets of numbers for right hand sidednahsets // set contains
    // unique attributes in left hand sideth
    // set contains unique attributes in right hand sidegir ni stnntem static
    // ArrayList<HashSet<Integer>> leftSide;
    static ArrayList<HashSet<Integer>> rightSide;
    static ArrayList<HashSet<Integer>> leftSide;

    // will
    // Initialize array listscontain all unique attributes in our relation
    static HashSet<Integer> num;

    static HashSet<Integer> numsFromLeftSide;
    static HashSet<Integer> numsFromRightSide;

    public static void main(String args[]) {
        // Split each line by semicolon
        // Get left hand side and right hand sideic void main (String[] args){

        // Save the first argument which is the text filename
        String txtFile = args[0];// Initialize set for numbersxtFile = args[0];

        // Split left hand side by comma try {

        // For each numerical string in left hand side// Create reader object suitable
        // for reading a text
        // file line by line

        // Split right hand side by comma leftSide = new ArrayList<HashSet<Integer>>();
        rightSide = new ArrayList<HashSet<Integer>>();

        // Read in line by line in the file

        try {
            BufferedReader in = new BufferedReader(new FileReader(txtFile));
            for (String line = in.readLine(); line != null; line = in.readLine()) {
                items = line.trim().split(";");

                numsFromLeftSide = new HashSet<Integer>();
                numsFromRightSide = new HashSet<Integer>();

                lhs = items[0].split(","); // Left hand side
                for (String num : lhs) {
                    numsFromLeftSide.add(Integer.valueOf(num));
                }

                rhs = items[1].split(","); // Right hand side
                for (String num : rhs) {
                    numsFromRightSide.add(Integer.valueOf(num));
                }

                leftSide.add(numsFromLeftSide);
                rightSide.add(numsFromRightSide);
            }

            for (HashSet<Integer> s : leftSide) {
                num.addAll(s);
            }

            for (HashSet<Integer> s : rightSide) {
                num.addAll(s);
            }

        } catch (IOException e) {
            System.out.println("ERROR!");
        }

        // finding out the size of the initial relation

        // find minimal basis given smt
        // returns minimal size
        int numAttributes = num.size();

        // Checking for the number of attributes
        // System.out.println("Size of set: " + numAttributes);
        FindMinBasis();
        partitionFDS();
    }

    /**
     * The endProgram method displays a message
     * to the user in cases where
     * the text file is in the wrong format
     * or the arguments are missing or not
     * correctly specified. Then it ends the
     * program in these scenarios.
     */
    public static void endProgram() {
        System.out.println("ERROR!");
        System.exit(0);
    }

    /*
     * Check if any singleton left side attributes match
     * If any matches are found, add the left side and right sides of each FD to
     * partitions
     * 
     */
    public static void partitionFDS() {
        // first FD
        for (int i = 0; i < leftSide.size(); i++) {
            // second FD
            for (int j = i + 1; j < leftSide.size(); j++) {

                // if first FD share the same elements as second FD
                if ((leftSide.get(i)).equals(leftSide.get(j))) {

                    // add the right side of second FD to first FD
                    rightSide.get(i).addAll(rightSide.get(j));

                    // delete the merged FD
                    leftSide.remove(j);
                    rightSide.remove(j);
                }
            }
        }
    }

    // find minimal basis for given input Fd's
    public static void FindMinBasis() {
        ArrayList<HashSet<Integer>> minLeftSide = new ArrayList<HashSet<Integer>>();
        ArrayList<HashSet<Integer>> minRightSide = new ArrayList<HashSet<Integer>>();

        // for all FD's
        for (int i = 0; i < leftSide.size(); i++) {
            // find elements that can directly be found with that FD
            HashSet<Integer> union = new HashSet<Integer>();
            union.addAll(leftSide.get(0));
            union.addAll(rightSide.get(0));

            // calculate closure with FD
            HashSet<Integer> withFD = FindClosure(union);

            // calculate closure without that FD
            HashSet<Integer> withoutFD = FindClosure(leftSide.get(0));

            // if they are NOT the same, add that FD to minimal basis
            if (!withoutFD.containsAll(withFD)) {
                minLeftSide.add(leftSide.get(i));
                minRightSide.add(rightSide.get(i));
            }
        }

        leftSide = minLeftSide;
        rightSide = minRightSide;
    }

    // for any set of attributes, this function returns its closure
    public static HashSet<Integer> FindClosure(HashSet<Integer> leftAtt) {
        HashSet<Integer> closure = new HashSet<Integer>();
        HashSet<Integer> initial = leftAtt;
        while (closure.size() != initial.size()) {
            // set closure to contents of initial array;
            closure = (HashSet<Integer>) initial.clone();

            // for every FD, check whther they are the same or not
            for (int i = 0; i < leftSide.size(); i++) {
                HashSet<Integer> union = new HashSet<Integer>();
                union.addAll(leftSide.get(0));
                union.addAll(closure);
                if (union.containsAll(closure)) {
                    closure.addAll(rightSide.get(i));
                }
            }
        }

        return closure;
    }

}
