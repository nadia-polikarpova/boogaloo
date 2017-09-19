echo "SYMBOLIC"
for file in examples/rv2013/verification_big/*
do
  echo
  echo $file
  echo
  time boogaloo -c=False $file
done

# echo "CONCRETE"
# for file in examples/rv2013/verification_big/*
# do
  # if [ "$file" != "examples/rv2013/verification_big/QuickSortPartial.bpl" ]; then
    # echo
    # echo $file
    # echo
    # time boogaloo -c=True $file
  # fi
# done