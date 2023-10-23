/*
Algorithm3.26: Synthesis of Third-Normal-Form Relations W ith a Lossless Join and Dependency Preservation.

INPUT: A relation R and a set F of functional dependencies that hold for R.

OUTPUT: A decomposition of R into a collection of relations, each of which is
in 3NF. The decomposition has the lossless-join and dependency-preservation
properties.

METHOD: Perform the following steps:
1. Find a minimal basis for F, say G.
2. Partition the the functional dependencies in G according to their left hand sides (so two dependencies X→A and X→B with the same left hand sides will be in the same partition). Merge each partition into a single FD using the combining rule (so X→A and X→B would become X→AB). For each rule X→Y that results from merging the rules of a partition, use XY as the schema of one of the relations in the decomposition. 
3. If none of the relation schemas from Step 2 is a superkey for R, add another relation whose schema is a key for R.
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

    // Regular expression intended for table column names
    static String REGEX = "[\\d,]+";
    // Use Pattern and Matcher to find instances where column names fail naming
    // rules
    static Pattern pat;
    static Matcher match;

    public static void main(String args[]) {
        // Split each line by semicolon
        // Get left hand side and right hand sideic void main (String[] args){

        // Check that we get exactly one arguement to the command
        if (args.length < 1 || args.length > 1) {
            endProgram();
        }
        String txtFile = args[0];// Initialize set for numbersxtFile = args[0];

        // Split left hand side by comma try {

        // For each numerical string in left hand side// Create reader object suitable
        // for reading a text
        // file line by line

        // Split right hand side by comma leftSide = new ArrayList<HashSet<Integer>>();
        num = new HashSet<Integer>();
        leftSide = new ArrayList<HashSet<Integer>>();
        rightSide = new ArrayList<HashSet<Integer>>();

        // Create a Pattern object for this specified REGEX
        pat = Pattern.compile(REGEX);

        // Read in line by line in the file
        try {
            BufferedReader in = new BufferedReader(new FileReader(txtFile));

            for (String line = in.readLine(); line != null; line = in.readLine()) {
                items = line.trim().split(";");

                if (items.length != 2) {
                    endProgram();
                }

                numsFromLeftSide = new HashSet<Integer>();
                numsFromRightSide = new HashSet<Integer>();

                // Create Matcher object in each iteration (for each column name)
                for (String item : items) {
                    match = pat.matcher(item);
                    // if string do not conform to the format
                    if (!match.matches()) {
                        endProgram();
                    }
                }

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
        // successfully created inital relations

        // Checking for the number of attributes
        // System.out.println("Size of set: " + numAttributes);

        FindMinBasis();

        partitionMergeFDs();

        HashSet<Integer> initRelation = new HashSet<Integer>();
        for (int i = 1; i <= numAttributes; i++) {
            initRelation.add(i);
        }

        // checks if relation is in 3NF
        ArrayList<HashSet<Integer>> relations = makesRInto3NF(initRelation);

        // check that no tables are subtables of other tables

        // print out the relations
        printRelations(relations);
    }

    /**
     * relations
     */
    private static void printRelations(ArrayList<HashSet<Integer>> relations) {
        // Iterate through each relation
        for (HashSet<Integer> s : relations) {
            // Create an array to contain numbers
            int[] nums = new int[s.size()];
            // Save numbers in set into array
            int i = 0;
            for (Integer n : s) {
                nums[i++] = n;
            }
            // Sort the number array
            Arrays.sort(nums);
            // Display numbers one by one, separated by comma
            for (int pos = 0; pos < nums.length; pos++) {
                System.out.print(nums[pos]);
                if (pos != nums.length - 1) {
                    System.out.print(",");
                }
            }
            // Print each relation on its own line
            System.out.println();
        }
    }

    private static ArrayList<HashSet<Integer>> makesRInto3NF(HashSet<Integer> initRelation) {
        ArrayList<HashSet<Integer>> output = new ArrayList<HashSet<Integer>>();
        output.add(initRelation);

        for (int i = 0; i < leftSide.size(); i++) {
            HashSet<Integer> insert = new HashSet<Integer>();
            insert.addAll(leftSide.get(i));
            insert.addAll(rightSide.get(i));
            output.add(insert);
        }
        output.remove(0);

        HashSet<Integer> checkForKey = hasSuperKey(output);
        if (checkForKey != null) {
            output.add(checkForKey);
        }

        return output;

    }

    /**
     * The endProgram method displays a message
     * to the user in cases where
     * the text file is not given
     * or the text file is in wrong format.
     * Then it ends the program in these scenarios.
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
    public static void partitionMergeFDs() {
        // first FD
        for (int i = 0; i < leftSide.size() - 1; i++) {
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

    public static HashSet<Integer> hasSuperKey(ArrayList<HashSet<Integer>> output) {
        // Check if the closure contains all the attributes in the relation
        // The number of unique attributes is found from num.size()
        // Check if closure.size() == num.size()
        boolean hasSuperKey = false;
        for (int i = 0; i < leftSide.size(); i++) {
            if (FindClosure(output.get(i), i).size() == num.size()) {
                hasSuperKey = true;
            }
        }

        // if no superkey, return a superkey
        if (!hasSuperKey) {
            int closest = 0;
            int indexClosest = 0;
            HashSet<Integer> key = new HashSet<Integer>();
            // Add a relation whose schema is a key for R
            for (int i = 0; i < leftSide.size(); i++) {
                // Try to find a relation whose closure contains all the unique attributes
                HashSet<Integer> candidateKey = FindClosure(leftSide.get(i));
                // If closure calculated without FDs equals num.size(), all the number of
                // attributes, add the set to something...

                if (closest < candidateKey.size()) {
                    key = leftSide.get(i);
                    closest = candidateKey.size();
                    indexClosest = i;
                }

            }

            HashSet<Integer> keyClosure = FindClosure(leftSide.get(indexClosest));
            HashSet<Integer> numCopy = new HashSet<Integer>(num);
            key.addAll(leftSide.get(indexClosest));
            numCopy.removeAll(keyClosure);
            key.addAll(numCopy);

            // the correct key/candidate key
            return key;
        }
        return null;
    }

    // find minimal basis for given input Fd's
    public static void FindMinBasis() {
        ArrayList<HashSet<Integer>> minLeftSide = new ArrayList<HashSet<Integer>>();
        ArrayList<HashSet<Integer>> minRightSide = new ArrayList<HashSet<Integer>>();

        // for all FD's
        for (int i = 0; i < leftSide.size(); i++) {
            // find elements that can directly be found with that FD
            HashSet<Integer> union = new HashSet<Integer>();
            union.addAll(leftSide.get(i));
            union.addAll(rightSide.get(i));
            // calculate closure with FD
            HashSet<Integer> withFD = FindClosure(union, i);
            // calculate closure without that FD
            HashSet<Integer> withoutFD = FindClosure(leftSide.get(i), i);
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
    public static HashSet<Integer> FindClosure(HashSet<Integer> leftAtt, Integer index) {
        // closure = x (leftAtt), olcClosure = empty set
        HashSet<Integer> closure = new HashSet<Integer>(leftAtt);
        HashSet<Integer> oldClosure = new HashSet<Integer>();
        // while x_old != x
        while (closure.size() != oldClosure.size()) {
            // set x_old to x
            oldClosure = new HashSet<Integer>(closure);

            // for each FD,
            for (int i = 0; i < leftSide.size(); i++) {
                // check whether the LHS attributes are in closure, but RHS attributes are not
                if ((i != index) && closure.containsAll(leftSide.get(i))) {
                    // Add RHS attributes into closure
                    closure.addAll(rightSide.get(i));
                }
            }
        }
        return closure;
    }

    // for any set of attributes, this function returns its closure
    public static HashSet<Integer> FindClosure(HashSet<Integer> leftAtt) {
        // closure = x (leftAtt), olcClosure = empty set
        HashSet<Integer> closure = new HashSet<Integer>(leftAtt);
        HashSet<Integer> oldClosure = new HashSet<Integer>();
        // while x_old != x
        while (closure.size() != oldClosure.size()) {
            // set x_old to x
            oldClosure = new HashSet<Integer>(closure);

            // for each FD,
            for (int i = 0; i < leftSide.size(); i++) {
                // check whether the LHS attributes are in closure, but RHS attributes are not
                if (closure.containsAll(leftSide.get(i))) {
                    // Add RHS attributes into closure
                    closure.addAll(rightSide.get(i));
                }
            }
        }
        return closure;
    }

}
