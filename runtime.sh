echo "SYMBOLIC"
for file in examples/rv2013/verification/*
do
  echo
  echo $file
  echo
  time boogaloo -c=False -b=Fair $file
done

# echo "CONCRETE"
# for file in examples/rv2013/verification/*
# do
  # if [ "$file" != "examples/rv2013/verification/QuickSortPartial.bpl" ]; then
    # echo
    # echo $file
    # echo
    # time boogaloo -c=True $file
  # fi
# done