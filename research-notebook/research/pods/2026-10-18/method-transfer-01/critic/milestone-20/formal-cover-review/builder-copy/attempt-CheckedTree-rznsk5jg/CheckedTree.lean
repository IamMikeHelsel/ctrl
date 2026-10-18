import SelectorSemantics
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
namespace E10
theorem node_1742 : Covered ((43 / 50 : ℚ),(22 / 25 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1741 : Covered ((87 / 100 : ℚ),(22 / 25 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1740 : Covered ((7 / 8 : ℚ),(22 / 25 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1739 : Covered ((351 / 400 : ℚ),(22 / 25 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1738 : Covered ((703 / 800 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1737 : Covered ((351 / 400 : ℚ),(703 / 800 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1736 : Covered ((351 / 400 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 exact split_c (351 / 400 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (49 / 1504 : ℚ) (703 / 800 : ℚ) node_1737 node_1738
theorem node_1735 : Covered ((351 / 400 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (351 / 400 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (49 / 1504 : ℚ) node_1736 node_1739
theorem node_1734 : Covered ((701 / 800 : ℚ),(351 / 400 : ℚ)) ((99 / 3008 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1733 : Covered ((701 / 800 : ℚ),(351 / 400 : ℚ)) ((49 / 1504 : ℚ),(99 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1732 : Covered ((701 / 800 : ℚ),(351 / 400 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (701 / 800 : ℚ) (351 / 400 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (99 / 3008 : ℚ) node_1733 node_1734
theorem node_1731 : Covered ((7 / 8 : ℚ),(701 / 800 : ℚ)) ((99 / 3008 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1730 : Covered ((7 / 8 : ℚ),(701 / 800 : ℚ)) ((49 / 1504 : ℚ),(99 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1729 : Covered ((7 / 8 : ℚ),(701 / 800 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (7 / 8 : ℚ) (701 / 800 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (99 / 3008 : ℚ) node_1730 node_1731
theorem node_1728 : Covered ((7 / 8 : ℚ),(351 / 400 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_c (7 / 8 : ℚ) (351 / 400 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (701 / 800 : ℚ) node_1729 node_1732
theorem node_1727 : Covered ((7 / 8 : ℚ),(351 / 400 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1726 : Covered ((7 / 8 : ℚ),(351 / 400 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (7 / 8 : ℚ) (351 / 400 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (49 / 1504 : ℚ) node_1727 node_1728
theorem node_1725 : Covered ((7 / 8 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_c (7 / 8 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (351 / 400 : ℚ) node_1726 node_1735
theorem node_1724 : Covered ((7 / 8 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (7 / 8 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (25 / 752 : ℚ) node_1725 node_1740
theorem node_1723 : Covered ((349 / 400 : ℚ),(7 / 8 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1722 : Covered ((87 / 100 : ℚ),(349 / 400 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1721 : Covered ((697 / 800 : ℚ),(349 / 400 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1720 : Covered ((87 / 100 : ℚ),(697 / 800 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1719 : Covered ((1393 / 1600 : ℚ),(697 / 800 : ℚ)) ((201 / 6016 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1718 : Covered ((1393 / 1600 : ℚ),(697 / 800 : ℚ)) ((25 / 752 : ℚ),(201 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1717 : Covered ((1393 / 1600 : ℚ),(697 / 800 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 exact split_j (1393 / 1600 : ℚ) (697 / 800 : ℚ) (25 / 752 : ℚ) (101 / 3008 : ℚ) (201 / 6016 : ℚ) node_1718 node_1719
theorem node_1716 : Covered ((87 / 100 : ℚ),(1393 / 1600 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1715 : Covered ((87 / 100 : ℚ),(697 / 800 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 exact split_c (87 / 100 : ℚ) (697 / 800 : ℚ) (25 / 752 : ℚ) (101 / 3008 : ℚ) (1393 / 1600 : ℚ) node_1716 node_1717
theorem node_1714 : Covered ((87 / 100 : ℚ),(697 / 800 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (87 / 100 : ℚ) (697 / 800 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (101 / 3008 : ℚ) node_1715 node_1720
theorem node_1713 : Covered ((87 / 100 : ℚ),(349 / 400 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_c (87 / 100 : ℚ) (349 / 400 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (697 / 800 : ℚ) node_1714 node_1721
theorem node_1712 : Covered ((87 / 100 : ℚ),(349 / 400 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (87 / 100 : ℚ) (349 / 400 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1713 node_1722
theorem node_1711 : Covered ((87 / 100 : ℚ),(7 / 8 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (87 / 100 : ℚ) (7 / 8 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (349 / 400 : ℚ) node_1712 node_1723
theorem node_1710 : Covered ((699 / 800 : ℚ),(7 / 8 : ℚ)) ((99 / 3008 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1709 : Covered ((699 / 800 : ℚ),(7 / 8 : ℚ)) ((49 / 1504 : ℚ),(99 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1708 : Covered ((699 / 800 : ℚ),(7 / 8 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (699 / 800 : ℚ) (7 / 8 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (99 / 3008 : ℚ) node_1709 node_1710
theorem node_1707 : Covered ((349 / 400 : ℚ),(699 / 800 : ℚ)) ((99 / 3008 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1706 : Covered ((349 / 400 : ℚ),(699 / 800 : ℚ)) ((49 / 1504 : ℚ),(99 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1705 : Covered ((349 / 400 : ℚ),(699 / 800 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (349 / 400 : ℚ) (699 / 800 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (99 / 3008 : ℚ) node_1706 node_1707
theorem node_1704 : Covered ((349 / 400 : ℚ),(7 / 8 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_c (349 / 400 : ℚ) (7 / 8 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (699 / 800 : ℚ) node_1705 node_1708
theorem node_1703 : Covered ((349 / 400 : ℚ),(7 / 8 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1702 : Covered ((349 / 400 : ℚ),(7 / 8 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (349 / 400 : ℚ) (7 / 8 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (49 / 1504 : ℚ) node_1703 node_1704
theorem node_1701 : Covered ((697 / 800 : ℚ),(349 / 400 : ℚ)) ((99 / 3008 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1700 : Covered ((697 / 800 : ℚ),(349 / 400 : ℚ)) ((49 / 1504 : ℚ),(99 / 3008 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1699 : Covered ((697 / 800 : ℚ),(349 / 400 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (697 / 800 : ℚ) (349 / 400 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (99 / 3008 : ℚ) node_1700 node_1701
theorem node_1698 : Covered ((87 / 100 : ℚ),(697 / 800 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1697 : Covered ((87 / 100 : ℚ),(349 / 400 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 exact split_c (87 / 100 : ℚ) (349 / 400 : ℚ) (49 / 1504 : ℚ) (25 / 752 : ℚ) (697 / 800 : ℚ) node_1698 node_1699
theorem node_1696 : Covered ((87 / 100 : ℚ),(349 / 400 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1695 : Covered ((87 / 100 : ℚ),(349 / 400 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (87 / 100 : ℚ) (349 / 400 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (49 / 1504 : ℚ) node_1696 node_1697
theorem node_1694 : Covered ((87 / 100 : ℚ),(7 / 8 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_c (87 / 100 : ℚ) (7 / 8 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (349 / 400 : ℚ) node_1695 node_1702
theorem node_1693 : Covered ((87 / 100 : ℚ),(7 / 8 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (87 / 100 : ℚ) (7 / 8 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (25 / 752 : ℚ) node_1694 node_1711
theorem node_1692 : Covered ((87 / 100 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (87 / 100 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (7 / 8 : ℚ) node_1693 node_1724
theorem node_1691 : Covered ((87 / 100 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (87 / 100 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (13 / 376 : ℚ) node_1692 node_1741
theorem node_1690 : Covered ((43 / 50 : ℚ),(87 / 100 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1689 : Covered ((347 / 400 : ℚ),(87 / 100 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1688 : Covered ((139 / 160 : ℚ),(87 / 100 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1687 : Covered ((139 / 160 : ℚ),(87 / 100 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1686 : Covered ((139 / 160 : ℚ),(87 / 100 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (139 / 160 : ℚ) (87 / 100 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (101 / 3008 : ℚ) node_1687 node_1688
theorem node_1685 : Covered ((1389 / 1600 : ℚ),(139 / 160 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1684 : Covered ((347 / 400 : ℚ),(1389 / 1600 : ℚ)) ((203 / 6016 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1683 : Covered ((347 / 400 : ℚ),(1389 / 1600 : ℚ)) ((101 / 3008 : ℚ),(203 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1682 : Covered ((347 / 400 : ℚ),(1389 / 1600 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (347 / 400 : ℚ) (1389 / 1600 : ℚ) (101 / 3008 : ℚ) (51 / 1504 : ℚ) (203 / 6016 : ℚ) node_1683 node_1684
theorem node_1681 : Covered ((347 / 400 : ℚ),(139 / 160 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_c (347 / 400 : ℚ) (139 / 160 : ℚ) (101 / 3008 : ℚ) (51 / 1504 : ℚ) (1389 / 1600 : ℚ) node_1682 node_1685
theorem node_1680 : Covered ((347 / 400 : ℚ),(139 / 160 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1679 : Covered ((347 / 400 : ℚ),(139 / 160 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (347 / 400 : ℚ) (139 / 160 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (101 / 3008 : ℚ) node_1680 node_1681
theorem node_1678 : Covered ((347 / 400 : ℚ),(87 / 100 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_c (347 / 400 : ℚ) (87 / 100 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (139 / 160 : ℚ) node_1679 node_1686
theorem node_1677 : Covered ((347 / 400 : ℚ),(87 / 100 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (347 / 400 : ℚ) (87 / 100 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1678 node_1689
theorem node_1676 : Covered ((693 / 800 : ℚ),(347 / 400 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1675 : Covered ((173 / 200 : ℚ),(693 / 800 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1674 : Covered ((277 / 320 : ℚ),(693 / 800 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1673 : Covered ((173 / 200 : ℚ),(277 / 320 : ℚ)) ((205 / 6016 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1672 : Covered ((173 / 200 : ℚ),(277 / 320 : ℚ)) ((51 / 1504 : ℚ),(205 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1671 : Covered ((173 / 200 : ℚ),(277 / 320 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_j (173 / 200 : ℚ) (277 / 320 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (205 / 6016 : ℚ) node_1672 node_1673
theorem node_1670 : Covered ((173 / 200 : ℚ),(693 / 800 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_c (173 / 200 : ℚ) (693 / 800 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (277 / 320 : ℚ) node_1671 node_1674
theorem node_1669 : Covered ((173 / 200 : ℚ),(693 / 800 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (173 / 200 : ℚ) (693 / 800 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1670 node_1675
theorem node_1668 : Covered ((173 / 200 : ℚ),(347 / 400 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (173 / 200 : ℚ) (347 / 400 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (693 / 800 : ℚ) node_1669 node_1676
theorem node_1667 : Covered ((1387 / 1600 : ℚ),(347 / 400 : ℚ)) ((203 / 6016 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1666 : Covered ((1387 / 1600 : ℚ),(347 / 400 : ℚ)) ((101 / 3008 : ℚ),(203 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1665 : Covered ((1387 / 1600 : ℚ),(347 / 400 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (1387 / 1600 : ℚ) (347 / 400 : ℚ) (101 / 3008 : ℚ) (51 / 1504 : ℚ) (203 / 6016 : ℚ) node_1666 node_1667
theorem node_1664 : Covered ((693 / 800 : ℚ),(1387 / 1600 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1663 : Covered ((693 / 800 : ℚ),(347 / 400 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_c (693 / 800 : ℚ) (347 / 400 : ℚ) (101 / 3008 : ℚ) (51 / 1504 : ℚ) (1387 / 1600 : ℚ) node_1664 node_1665
theorem node_1662 : Covered ((693 / 800 : ℚ),(347 / 400 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1661 : Covered ((693 / 800 : ℚ),(347 / 400 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (693 / 800 : ℚ) (347 / 400 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (101 / 3008 : ℚ) node_1662 node_1663
theorem node_1660 : Covered ((173 / 200 : ℚ),(693 / 800 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1659 : Covered ((173 / 200 : ℚ),(693 / 800 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1658 : Covered ((173 / 200 : ℚ),(693 / 800 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (173 / 200 : ℚ) (693 / 800 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (101 / 3008 : ℚ) node_1659 node_1660
theorem node_1657 : Covered ((173 / 200 : ℚ),(347 / 400 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_c (173 / 200 : ℚ) (347 / 400 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (693 / 800 : ℚ) node_1658 node_1661
theorem node_1656 : Covered ((173 / 200 : ℚ),(347 / 400 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (173 / 200 : ℚ) (347 / 400 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1657 node_1668
theorem node_1655 : Covered ((173 / 200 : ℚ),(87 / 100 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (173 / 200 : ℚ) (87 / 100 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (347 / 400 : ℚ) node_1656 node_1677
theorem node_1654 : Covered ((347 / 400 : ℚ),(87 / 100 : ℚ)) ((49 / 1504 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1653 : Covered ((347 / 400 : ℚ),(87 / 100 : ℚ)) ((3 / 94 : ℚ),(49 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1652 : Covered ((347 / 400 : ℚ),(87 / 100 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_j (347 / 400 : ℚ) (87 / 100 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (49 / 1504 : ℚ) node_1653 node_1654
theorem node_1651 : Covered ((173 / 200 : ℚ),(347 / 400 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1650 : Covered ((173 / 200 : ℚ),(87 / 100 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 exact split_c (173 / 200 : ℚ) (87 / 100 : ℚ) (3 / 94 : ℚ) (25 / 752 : ℚ) (347 / 400 : ℚ) node_1651 node_1652
theorem node_1649 : Covered ((173 / 200 : ℚ),(87 / 100 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (173 / 200 : ℚ) (87 / 100 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (25 / 752 : ℚ) node_1650 node_1655
theorem node_1648 : Covered ((691 / 800 : ℚ),(173 / 200 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1647 : Covered ((1383 / 1600 : ℚ),(173 / 200 : ℚ)) ((205 / 6016 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1646 : Covered ((1383 / 1600 : ℚ),(173 / 200 : ℚ)) ((51 / 1504 : ℚ),(205 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1645 : Covered ((1383 / 1600 : ℚ),(173 / 200 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_j (1383 / 1600 : ℚ) (173 / 200 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (205 / 6016 : ℚ) node_1646 node_1647
theorem node_1644 : Covered ((691 / 800 : ℚ),(1383 / 1600 : ℚ)) ((205 / 6016 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1643 : Covered ((691 / 800 : ℚ),(1383 / 1600 : ℚ)) ((51 / 1504 : ℚ),(205 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1642 : Covered ((691 / 800 : ℚ),(1383 / 1600 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_j (691 / 800 : ℚ) (1383 / 1600 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (205 / 6016 : ℚ) node_1643 node_1644
theorem node_1641 : Covered ((691 / 800 : ℚ),(173 / 200 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_c (691 / 800 : ℚ) (173 / 200 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (1383 / 1600 : ℚ) node_1642 node_1645
theorem node_1640 : Covered ((691 / 800 : ℚ),(173 / 200 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (691 / 800 : ℚ) (173 / 200 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1641 node_1648
theorem node_1639 : Covered ((69 / 80 : ℚ),(691 / 800 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1638 : Covered ((1381 / 1600 : ℚ),(691 / 800 : ℚ)) ((205 / 6016 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1637 : Covered ((1381 / 1600 : ℚ),(691 / 800 : ℚ)) ((51 / 1504 : ℚ),(205 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1636 : Covered ((1381 / 1600 : ℚ),(691 / 800 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_j (1381 / 1600 : ℚ) (691 / 800 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (205 / 6016 : ℚ) node_1637 node_1638
theorem node_1635 : Covered ((69 / 80 : ℚ),(1381 / 1600 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1634 : Covered ((69 / 80 : ℚ),(691 / 800 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 exact split_c (69 / 80 : ℚ) (691 / 800 : ℚ) (51 / 1504 : ℚ) (103 / 3008 : ℚ) (1381 / 1600 : ℚ) node_1635 node_1636
theorem node_1633 : Covered ((69 / 80 : ℚ),(691 / 800 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (69 / 80 : ℚ) (691 / 800 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1634 node_1639
theorem node_1632 : Covered ((69 / 80 : ℚ),(173 / 200 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (69 / 80 : ℚ) (173 / 200 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (691 / 800 : ℚ) node_1633 node_1640
theorem node_1631 : Covered ((691 / 800 : ℚ),(173 / 200 : ℚ)) ((101 / 3008 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1630 : Covered ((691 / 800 : ℚ),(173 / 200 : ℚ)) ((25 / 752 : ℚ),(101 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1629 : Covered ((691 / 800 : ℚ),(173 / 200 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_j (691 / 800 : ℚ) (173 / 200 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (101 / 3008 : ℚ) node_1630 node_1631
theorem node_1628 : Covered ((69 / 80 : ℚ),(691 / 800 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1627 : Covered ((69 / 80 : ℚ),(173 / 200 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 exact split_c (69 / 80 : ℚ) (173 / 200 : ℚ) (25 / 752 : ℚ) (51 / 1504 : ℚ) (691 / 800 : ℚ) node_1628 node_1629
theorem node_1626 : Covered ((69 / 80 : ℚ),(173 / 200 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (69 / 80 : ℚ) (173 / 200 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1627 node_1632
theorem node_1625 : Covered ((1379 / 1600 : ℚ),(69 / 80 : ℚ)) ((207 / 6016 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1624 : Covered ((1379 / 1600 : ℚ),(69 / 80 : ℚ)) ((103 / 3008 : ℚ),(207 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1623 : Covered ((1379 / 1600 : ℚ),(69 / 80 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (1379 / 1600 : ℚ) (69 / 80 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (207 / 6016 : ℚ) node_1624 node_1625
theorem node_1622 : Covered ((689 / 800 : ℚ),(1379 / 1600 : ℚ)) ((207 / 6016 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1621 : Covered ((689 / 800 : ℚ),(1379 / 1600 : ℚ)) ((103 / 3008 : ℚ),(207 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1620 : Covered ((689 / 800 : ℚ),(1379 / 1600 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (689 / 800 : ℚ) (1379 / 1600 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (207 / 6016 : ℚ) node_1621 node_1622
theorem node_1619 : Covered ((689 / 800 : ℚ),(69 / 80 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (689 / 800 : ℚ) (69 / 80 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (1379 / 1600 : ℚ) node_1620 node_1623
theorem node_1618 : Covered ((689 / 800 : ℚ),(69 / 80 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1617 : Covered ((689 / 800 : ℚ),(69 / 80 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (689 / 800 : ℚ) (69 / 80 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1618 node_1619
theorem node_1616 : Covered ((1377 / 1600 : ℚ),(689 / 800 : ℚ)) ((207 / 6016 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1615 : Covered ((1377 / 1600 : ℚ),(689 / 800 : ℚ)) ((103 / 3008 : ℚ),(207 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1614 : Covered ((1377 / 1600 : ℚ),(689 / 800 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (1377 / 1600 : ℚ) (689 / 800 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (207 / 6016 : ℚ) node_1615 node_1616
theorem node_1613 : Covered ((43 / 50 : ℚ),(1377 / 1600 : ℚ)) ((207 / 6016 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1612 : Covered ((43 / 50 : ℚ),(1377 / 1600 : ℚ)) ((103 / 3008 : ℚ),(207 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1611 : Covered ((43 / 50 : ℚ),(1377 / 1600 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (43 / 50 : ℚ) (1377 / 1600 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (207 / 6016 : ℚ) node_1612 node_1613
theorem node_1610 : Covered ((43 / 50 : ℚ),(689 / 800 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (43 / 50 : ℚ) (689 / 800 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (1377 / 1600 : ℚ) node_1611 node_1614
theorem node_1609 : Covered ((43 / 50 : ℚ),(689 / 800 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1608 : Covered ((43 / 50 : ℚ),(689 / 800 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (43 / 50 : ℚ) (689 / 800 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1609 node_1610
theorem node_1607 : Covered ((43 / 50 : ℚ),(69 / 80 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (43 / 50 : ℚ) (69 / 80 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (689 / 800 : ℚ) node_1608 node_1617
theorem node_1606 : Covered ((43 / 50 : ℚ),(69 / 80 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1605 : Covered ((43 / 50 : ℚ),(69 / 80 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (43 / 50 : ℚ) (69 / 80 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1606 node_1607
theorem node_1604 : Covered ((43 / 50 : ℚ),(173 / 200 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (43 / 50 : ℚ) (173 / 200 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (69 / 80 : ℚ) node_1605 node_1626
theorem node_1603 : Covered ((43 / 50 : ℚ),(173 / 200 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1602 : Covered ((43 / 50 : ℚ),(173 / 200 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (43 / 50 : ℚ) (173 / 200 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (25 / 752 : ℚ) node_1603 node_1604
theorem node_1601 : Covered ((43 / 50 : ℚ),(87 / 100 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (43 / 50 : ℚ) (87 / 100 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (173 / 200 : ℚ) node_1602 node_1649
theorem node_1600 : Covered ((43 / 50 : ℚ),(87 / 100 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (43 / 50 : ℚ) (87 / 100 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (13 / 376 : ℚ) node_1601 node_1690
theorem node_1599 : Covered ((43 / 50 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (43 / 50 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (87 / 100 : ℚ) node_1600 node_1691
theorem node_1598 : Covered ((43 / 50 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (43 / 50 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_1599 node_1742
theorem node_1597 : Covered ((21 / 25 : ℚ),(43 / 50 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1596 : Covered ((171 / 200 : ℚ),(43 / 50 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1595 : Covered ((343 / 400 : ℚ),(43 / 50 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1594 : Covered ((687 / 800 : ℚ),(43 / 50 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1593 : Covered ((55 / 64 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1592 : Covered ((687 / 800 : ℚ),(55 / 64 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1591 : Covered ((687 / 800 : ℚ),(55 / 64 : ℚ)) ((13 / 376 : ℚ),(209 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1590 : Covered ((687 / 800 : ℚ),(55 / 64 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_j (687 / 800 : ℚ) (55 / 64 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (209 / 6016 : ℚ) node_1591 node_1592
theorem node_1589 : Covered ((687 / 800 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_c (687 / 800 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (55 / 64 : ℚ) node_1590 node_1593
theorem node_1588 : Covered ((687 / 800 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (687 / 800 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1589 node_1594
theorem node_1587 : Covered ((343 / 400 : ℚ),(687 / 800 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1586 : Covered ((1373 / 1600 : ℚ),(687 / 800 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1585 : Covered ((1373 / 1600 : ℚ),(687 / 800 : ℚ)) ((13 / 376 : ℚ),(209 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1584 : Covered ((1373 / 1600 : ℚ),(687 / 800 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_j (1373 / 1600 : ℚ) (687 / 800 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (209 / 6016 : ℚ) node_1585 node_1586
theorem node_1583 : Covered ((549 / 640 : ℚ),(1373 / 1600 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1582 : Covered ((343 / 400 : ℚ),(549 / 640 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1581 : Covered ((343 / 400 : ℚ),(1373 / 1600 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_c (343 / 400 : ℚ) (1373 / 1600 : ℚ) (209 / 6016 : ℚ) (105 / 3008 : ℚ) (549 / 640 : ℚ) node_1582 node_1583
theorem node_1580 : Covered ((343 / 400 : ℚ),(1373 / 1600 : ℚ)) ((13 / 376 : ℚ),(209 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1579 : Covered ((343 / 400 : ℚ),(1373 / 1600 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_j (343 / 400 : ℚ) (1373 / 1600 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (209 / 6016 : ℚ) node_1580 node_1581
theorem node_1578 : Covered ((343 / 400 : ℚ),(687 / 800 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_c (343 / 400 : ℚ) (687 / 800 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (1373 / 1600 : ℚ) node_1579 node_1584
theorem node_1577 : Covered ((343 / 400 : ℚ),(687 / 800 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (343 / 400 : ℚ) (687 / 800 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1578 node_1587
theorem node_1576 : Covered ((343 / 400 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (343 / 400 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (687 / 800 : ℚ) node_1577 node_1588
theorem node_1575 : Covered ((343 / 400 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (343 / 400 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1576 node_1595
theorem node_1574 : Covered ((171 / 200 : ℚ),(343 / 400 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1573 : Covered ((1371 / 1600 : ℚ),(343 / 400 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1572 : Covered ((137 / 160 : ℚ),(1371 / 1600 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1571 : Covered ((2741 / 3200 : ℚ),(1371 / 1600 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1570 : Covered ((137 / 160 : ℚ),(2741 / 3200 : ℚ)) ((421 / 12032 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1569 : Covered ((137 / 160 : ℚ),(2741 / 3200 : ℚ)) ((105 / 3008 : ℚ),(421 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1568 : Covered ((137 / 160 : ℚ),(2741 / 3200 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 exact split_j (137 / 160 : ℚ) (2741 / 3200 : ℚ) (105 / 3008 : ℚ) (211 / 6016 : ℚ) (421 / 12032 : ℚ) node_1569 node_1570
theorem node_1567 : Covered ((137 / 160 : ℚ),(1371 / 1600 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 exact split_c (137 / 160 : ℚ) (1371 / 1600 : ℚ) (105 / 3008 : ℚ) (211 / 6016 : ℚ) (2741 / 3200 : ℚ) node_1568 node_1571
theorem node_1566 : Covered ((137 / 160 : ℚ),(1371 / 1600 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (137 / 160 : ℚ) (1371 / 1600 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (211 / 6016 : ℚ) node_1567 node_1572
theorem node_1565 : Covered ((137 / 160 : ℚ),(343 / 400 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (137 / 160 : ℚ) (343 / 400 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (1371 / 1600 : ℚ) node_1566 node_1573
theorem node_1564 : Covered ((1371 / 1600 : ℚ),(343 / 400 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1563 : Covered ((1371 / 1600 : ℚ),(343 / 400 : ℚ)) ((13 / 376 : ℚ),(209 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1562 : Covered ((1371 / 1600 : ℚ),(343 / 400 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_j (1371 / 1600 : ℚ) (343 / 400 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (209 / 6016 : ℚ) node_1563 node_1564
theorem node_1561 : Covered ((137 / 160 : ℚ),(1371 / 1600 : ℚ)) ((209 / 6016 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1560 : Covered ((137 / 160 : ℚ),(1371 / 1600 : ℚ)) ((13 / 376 : ℚ),(209 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1559 : Covered ((137 / 160 : ℚ),(1371 / 1600 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_j (137 / 160 : ℚ) (1371 / 1600 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (209 / 6016 : ℚ) node_1560 node_1561
theorem node_1558 : Covered ((137 / 160 : ℚ),(343 / 400 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 exact split_c (137 / 160 : ℚ) (343 / 400 : ℚ) (13 / 376 : ℚ) (105 / 3008 : ℚ) (1371 / 1600 : ℚ) node_1559 node_1562
theorem node_1557 : Covered ((137 / 160 : ℚ),(343 / 400 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (137 / 160 : ℚ) (343 / 400 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1558 node_1565
theorem node_1556 : Covered ((1369 / 1600 : ℚ),(137 / 160 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1555 : Covered ((1369 / 1600 : ℚ),(137 / 160 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1554 : Covered ((1369 / 1600 : ℚ),(137 / 160 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (1369 / 1600 : ℚ) (137 / 160 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (211 / 6016 : ℚ) node_1555 node_1556
theorem node_1553 : Covered ((171 / 200 : ℚ),(1369 / 1600 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1552 : Covered ((171 / 200 : ℚ),(1369 / 1600 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1551 : Covered ((171 / 200 : ℚ),(1369 / 1600 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (171 / 200 : ℚ) (1369 / 1600 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (211 / 6016 : ℚ) node_1552 node_1553
theorem node_1550 : Covered ((171 / 200 : ℚ),(137 / 160 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (171 / 200 : ℚ) (137 / 160 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (1369 / 1600 : ℚ) node_1551 node_1554
theorem node_1549 : Covered ((171 / 200 : ℚ),(137 / 160 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1548 : Covered ((171 / 200 : ℚ),(137 / 160 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (171 / 200 : ℚ) (137 / 160 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1549 node_1550
theorem node_1547 : Covered ((171 / 200 : ℚ),(343 / 400 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (171 / 200 : ℚ) (343 / 400 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (137 / 160 : ℚ) node_1548 node_1557
theorem node_1546 : Covered ((171 / 200 : ℚ),(343 / 400 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (171 / 200 : ℚ) (343 / 400 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1547 node_1574
theorem node_1545 : Covered ((171 / 200 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (171 / 200 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (343 / 400 : ℚ) node_1546 node_1575
theorem node_1544 : Covered ((171 / 200 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (171 / 200 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_1545 node_1596
theorem node_1543 : Covered ((17 / 20 : ℚ),(171 / 200 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1542 : Covered ((683 / 800 : ℚ),(171 / 200 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1541 : Covered ((341 / 400 : ℚ),(683 / 800 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1540 : Covered ((273 / 320 : ℚ),(683 / 800 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1539 : Covered ((2731 / 3200 : ℚ),(683 / 800 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1538 : Covered ((273 / 320 : ℚ),(2731 / 3200 : ℚ)) ((425 / 12032 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1537 : Covered ((273 / 320 : ℚ),(2731 / 3200 : ℚ)) ((53 / 1504 : ℚ),(425 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1536 : Covered ((273 / 320 : ℚ),(2731 / 3200 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 exact split_j (273 / 320 : ℚ) (2731 / 3200 : ℚ) (53 / 1504 : ℚ) (213 / 6016 : ℚ) (425 / 12032 : ℚ) node_1537 node_1538
theorem node_1535 : Covered ((273 / 320 : ℚ),(683 / 800 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 exact split_c (273 / 320 : ℚ) (683 / 800 : ℚ) (53 / 1504 : ℚ) (213 / 6016 : ℚ) (2731 / 3200 : ℚ) node_1536 node_1539
theorem node_1534 : Covered ((273 / 320 : ℚ),(683 / 800 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (273 / 320 : ℚ) (683 / 800 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1535 node_1540
theorem node_1533 : Covered ((341 / 400 : ℚ),(273 / 320 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1532 : Covered ((2729 / 3200 : ℚ),(273 / 320 : ℚ)) ((425 / 12032 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1531 : Covered ((2729 / 3200 : ℚ),(273 / 320 : ℚ)) ((53 / 1504 : ℚ),(425 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1530 : Covered ((2729 / 3200 : ℚ),(273 / 320 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 exact split_j (2729 / 3200 : ℚ) (273 / 320 : ℚ) (53 / 1504 : ℚ) (213 / 6016 : ℚ) (425 / 12032 : ℚ) node_1531 node_1532
theorem node_1529 : Covered ((341 / 400 : ℚ),(2729 / 3200 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1528 : Covered ((341 / 400 : ℚ),(273 / 320 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 exact split_c (341 / 400 : ℚ) (273 / 320 : ℚ) (53 / 1504 : ℚ) (213 / 6016 : ℚ) (2729 / 3200 : ℚ) node_1529 node_1530
theorem node_1527 : Covered ((341 / 400 : ℚ),(273 / 320 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (341 / 400 : ℚ) (273 / 320 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1528 node_1533
theorem node_1526 : Covered ((341 / 400 : ℚ),(683 / 800 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (341 / 400 : ℚ) (683 / 800 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (273 / 320 : ℚ) node_1527 node_1534
theorem node_1525 : Covered ((341 / 400 : ℚ),(683 / 800 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (341 / 400 : ℚ) (683 / 800 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1526 node_1541
theorem node_1524 : Covered ((341 / 400 : ℚ),(171 / 200 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (341 / 400 : ℚ) (171 / 200 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (683 / 800 : ℚ) node_1525 node_1542
theorem node_1523 : Covered ((547 / 640 : ℚ),(171 / 200 : ℚ)) ((9 / 256 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1522 : Covered ((547 / 640 : ℚ),(171 / 200 : ℚ)) ((211 / 6016 : ℚ),(9 / 256 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1521 : Covered ((547 / 640 : ℚ),(171 / 200 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (547 / 640 : ℚ) (171 / 200 : ℚ) (211 / 6016 : ℚ) (53 / 1504 : ℚ) (9 / 256 : ℚ) node_1522 node_1523
theorem node_1520 : Covered ((1367 / 1600 : ℚ),(547 / 640 : ℚ)) ((9 / 256 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1519 : Covered ((1367 / 1600 : ℚ),(547 / 640 : ℚ)) ((211 / 6016 : ℚ),(9 / 256 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1518 : Covered ((1367 / 1600 : ℚ),(547 / 640 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (1367 / 1600 : ℚ) (547 / 640 : ℚ) (211 / 6016 : ℚ) (53 / 1504 : ℚ) (9 / 256 : ℚ) node_1519 node_1520
theorem node_1517 : Covered ((1367 / 1600 : ℚ),(171 / 200 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (1367 / 1600 : ℚ) (171 / 200 : ℚ) (211 / 6016 : ℚ) (53 / 1504 : ℚ) (547 / 640 : ℚ) node_1518 node_1521
theorem node_1516 : Covered ((1367 / 1600 : ℚ),(171 / 200 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1515 : Covered ((1367 / 1600 : ℚ),(171 / 200 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (1367 / 1600 : ℚ) (171 / 200 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (211 / 6016 : ℚ) node_1516 node_1517
theorem node_1514 : Covered ((683 / 800 : ℚ),(1367 / 1600 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1513 : Covered ((683 / 800 : ℚ),(1367 / 1600 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1512 : Covered ((683 / 800 : ℚ),(1367 / 1600 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (683 / 800 : ℚ) (1367 / 1600 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (211 / 6016 : ℚ) node_1513 node_1514
theorem node_1511 : Covered ((683 / 800 : ℚ),(171 / 200 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (683 / 800 : ℚ) (171 / 200 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (1367 / 1600 : ℚ) node_1512 node_1515
theorem node_1510 : Covered ((683 / 800 : ℚ),(171 / 200 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1509 : Covered ((683 / 800 : ℚ),(171 / 200 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (683 / 800 : ℚ) (171 / 200 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1510 node_1511
theorem node_1508 : Covered ((273 / 320 : ℚ),(683 / 800 : ℚ)) ((211 / 6016 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1507 : Covered ((273 / 320 : ℚ),(683 / 800 : ℚ)) ((105 / 3008 : ℚ),(211 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1506 : Covered ((273 / 320 : ℚ),(683 / 800 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (273 / 320 : ℚ) (683 / 800 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (211 / 6016 : ℚ) node_1507 node_1508
theorem node_1505 : Covered ((341 / 400 : ℚ),(273 / 320 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1504 : Covered ((341 / 400 : ℚ),(683 / 800 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (341 / 400 : ℚ) (683 / 800 : ℚ) (105 / 3008 : ℚ) (53 / 1504 : ℚ) (273 / 320 : ℚ) node_1505 node_1506
theorem node_1503 : Covered ((341 / 400 : ℚ),(683 / 800 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1502 : Covered ((341 / 400 : ℚ),(683 / 800 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (341 / 400 : ℚ) (683 / 800 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1503 node_1504
theorem node_1501 : Covered ((341 / 400 : ℚ),(171 / 200 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (341 / 400 : ℚ) (171 / 200 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (683 / 800 : ℚ) node_1502 node_1509
theorem node_1500 : Covered ((341 / 400 : ℚ),(171 / 200 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (341 / 400 : ℚ) (171 / 200 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1501 node_1524
theorem node_1499 : Covered ((681 / 800 : ℚ),(341 / 400 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1498 : Covered ((2727 / 3200 : ℚ),(341 / 400 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1497 : Covered ((1363 / 1600 : ℚ),(2727 / 3200 : ℚ)) ((427 / 12032 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1496 : Covered ((1363 / 1600 : ℚ),(2727 / 3200 : ℚ)) ((213 / 6016 : ℚ),(427 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1495 : Covered ((1363 / 1600 : ℚ),(2727 / 3200 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (1363 / 1600 : ℚ) (2727 / 3200 : ℚ) (213 / 6016 : ℚ) (107 / 3008 : ℚ) (427 / 12032 : ℚ) node_1496 node_1497
theorem node_1494 : Covered ((1363 / 1600 : ℚ),(341 / 400 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (1363 / 1600 : ℚ) (341 / 400 : ℚ) (213 / 6016 : ℚ) (107 / 3008 : ℚ) (2727 / 3200 : ℚ) node_1495 node_1498
theorem node_1493 : Covered ((1363 / 1600 : ℚ),(341 / 400 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1492 : Covered ((1363 / 1600 : ℚ),(341 / 400 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (1363 / 1600 : ℚ) (341 / 400 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1493 node_1494
theorem node_1491 : Covered ((109 / 128 : ℚ),(1363 / 1600 : ℚ)) ((427 / 12032 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1490 : Covered ((109 / 128 : ℚ),(1363 / 1600 : ℚ)) ((213 / 6016 : ℚ),(427 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1489 : Covered ((109 / 128 : ℚ),(1363 / 1600 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (109 / 128 : ℚ) (1363 / 1600 : ℚ) (213 / 6016 : ℚ) (107 / 3008 : ℚ) (427 / 12032 : ℚ) node_1490 node_1491
theorem node_1488 : Covered ((681 / 800 : ℚ),(109 / 128 : ℚ)) ((427 / 12032 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1487 : Covered ((681 / 800 : ℚ),(109 / 128 : ℚ)) ((213 / 6016 : ℚ),(427 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1486 : Covered ((681 / 800 : ℚ),(109 / 128 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (681 / 800 : ℚ) (109 / 128 : ℚ) (213 / 6016 : ℚ) (107 / 3008 : ℚ) (427 / 12032 : ℚ) node_1487 node_1488
theorem node_1485 : Covered ((681 / 800 : ℚ),(1363 / 1600 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (681 / 800 : ℚ) (1363 / 1600 : ℚ) (213 / 6016 : ℚ) (107 / 3008 : ℚ) (109 / 128 : ℚ) node_1486 node_1489
theorem node_1484 : Covered ((681 / 800 : ℚ),(1363 / 1600 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1483 : Covered ((681 / 800 : ℚ),(1363 / 1600 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (681 / 800 : ℚ) (1363 / 1600 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1484 node_1485
theorem node_1482 : Covered ((681 / 800 : ℚ),(341 / 400 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (681 / 800 : ℚ) (341 / 400 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (1363 / 1600 : ℚ) node_1483 node_1492
theorem node_1481 : Covered ((681 / 800 : ℚ),(341 / 400 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (681 / 800 : ℚ) (341 / 400 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1482 node_1499
theorem node_1480 : Covered ((1361 / 1600 : ℚ),(681 / 800 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1479 : Covered ((17 / 20 : ℚ),(1361 / 1600 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1478 : Covered ((2721 / 3200 : ℚ),(1361 / 1600 : ℚ)) ((429 / 12032 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1477 : Covered ((2721 / 3200 : ℚ),(1361 / 1600 : ℚ)) ((107 / 3008 : ℚ),(429 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1476 : Covered ((2721 / 3200 : ℚ),(1361 / 1600 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 exact split_j (2721 / 3200 : ℚ) (1361 / 1600 : ℚ) (107 / 3008 : ℚ) (215 / 6016 : ℚ) (429 / 12032 : ℚ) node_1477 node_1478
theorem node_1475 : Covered ((17 / 20 : ℚ),(2721 / 3200 : ℚ)) ((429 / 12032 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1474 : Covered ((17 / 20 : ℚ),(2721 / 3200 : ℚ)) ((107 / 3008 : ℚ),(429 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1473 : Covered ((17 / 20 : ℚ),(2721 / 3200 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (2721 / 3200 : ℚ) (107 / 3008 : ℚ) (215 / 6016 : ℚ) (429 / 12032 : ℚ) node_1474 node_1475
theorem node_1472 : Covered ((17 / 20 : ℚ),(1361 / 1600 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (1361 / 1600 : ℚ) (107 / 3008 : ℚ) (215 / 6016 : ℚ) (2721 / 3200 : ℚ) node_1473 node_1476
theorem node_1471 : Covered ((17 / 20 : ℚ),(1361 / 1600 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (1361 / 1600 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1472 node_1479
theorem node_1470 : Covered ((17 / 20 : ℚ),(681 / 800 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (681 / 800 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (1361 / 1600 : ℚ) node_1471 node_1480
theorem node_1469 : Covered ((2723 / 3200 : ℚ),(681 / 800 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1468 : Covered ((1361 / 1600 : ℚ),(2723 / 3200 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1467 : Covered ((1361 / 1600 : ℚ),(681 / 800 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (1361 / 1600 : ℚ) (681 / 800 : ℚ) (213 / 6016 : ℚ) (107 / 3008 : ℚ) (2723 / 3200 : ℚ) node_1468 node_1469
theorem node_1466 : Covered ((1361 / 1600 : ℚ),(681 / 800 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1465 : Covered ((1361 / 1600 : ℚ),(681 / 800 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (1361 / 1600 : ℚ) (681 / 800 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1466 node_1467
theorem node_1464 : Covered ((17 / 20 : ℚ),(1361 / 1600 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1463 : Covered ((17 / 20 : ℚ),(1361 / 1600 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1462 : Covered ((17 / 20 : ℚ),(1361 / 1600 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (1361 / 1600 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1463 node_1464
theorem node_1461 : Covered ((17 / 20 : ℚ),(681 / 800 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (681 / 800 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (1361 / 1600 : ℚ) node_1462 node_1465
theorem node_1460 : Covered ((17 / 20 : ℚ),(681 / 800 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (681 / 800 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1461 node_1470
theorem node_1459 : Covered ((17 / 20 : ℚ),(341 / 400 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (341 / 400 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (681 / 800 : ℚ) node_1460 node_1481
theorem node_1458 : Covered ((681 / 800 : ℚ),(341 / 400 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1457 : Covered ((681 / 800 : ℚ),(341 / 400 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1456 : Covered ((681 / 800 : ℚ),(341 / 400 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (681 / 800 : ℚ) (341 / 400 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1457 node_1458
theorem node_1455 : Covered ((17 / 20 : ℚ),(681 / 800 : ℚ)) ((105 / 3008 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1454 : Covered ((17 / 20 : ℚ),(681 / 800 : ℚ)) ((13 / 376 : ℚ),(105 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1453 : Covered ((17 / 20 : ℚ),(681 / 800 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (681 / 800 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (105 / 3008 : ℚ) node_1454 node_1455
theorem node_1452 : Covered ((17 / 20 : ℚ),(341 / 400 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (341 / 400 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (681 / 800 : ℚ) node_1453 node_1456
theorem node_1451 : Covered ((17 / 20 : ℚ),(341 / 400 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (341 / 400 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1452 node_1459
theorem node_1450 : Covered ((17 / 20 : ℚ),(171 / 200 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (171 / 200 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (341 / 400 : ℚ) node_1451 node_1500
theorem node_1449 : Covered ((17 / 20 : ℚ),(171 / 200 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (171 / 200 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_1450 node_1543
theorem node_1448 : Covered ((17 / 20 : ℚ),(43 / 50 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (43 / 50 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (171 / 200 : ℚ) node_1449 node_1544
theorem node_1447 : Covered ((55 / 64 : ℚ),(43 / 50 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1446 : Covered ((687 / 800 : ℚ),(55 / 64 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1445 : Covered ((687 / 800 : ℚ),(43 / 50 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (687 / 800 : ℚ) (43 / 50 : ℚ) (103 / 3008 : ℚ) (13 / 376 : ℚ) (55 / 64 : ℚ) node_1446 node_1447
theorem node_1444 : Covered ((687 / 800 : ℚ),(43 / 50 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1443 : Covered ((687 / 800 : ℚ),(43 / 50 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (687 / 800 : ℚ) (43 / 50 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1444 node_1445
theorem node_1442 : Covered ((343 / 400 : ℚ),(687 / 800 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1441 : Covered ((343 / 400 : ℚ),(687 / 800 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1440 : Covered ((343 / 400 : ℚ),(687 / 800 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (343 / 400 : ℚ) (687 / 800 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1441 node_1442
theorem node_1439 : Covered ((343 / 400 : ℚ),(43 / 50 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (343 / 400 : ℚ) (43 / 50 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (687 / 800 : ℚ) node_1440 node_1443
theorem node_1438 : Covered ((343 / 400 : ℚ),(43 / 50 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1437 : Covered ((343 / 400 : ℚ),(43 / 50 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (343 / 400 : ℚ) (43 / 50 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1438 node_1439
theorem node_1436 : Covered ((137 / 160 : ℚ),(343 / 400 : ℚ)) ((103 / 3008 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1435 : Covered ((137 / 160 : ℚ),(343 / 400 : ℚ)) ((51 / 1504 : ℚ),(103 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1434 : Covered ((137 / 160 : ℚ),(343 / 400 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (137 / 160 : ℚ) (343 / 400 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (103 / 3008 : ℚ) node_1435 node_1436
theorem node_1433 : Covered ((171 / 200 : ℚ),(137 / 160 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1432 : Covered ((171 / 200 : ℚ),(343 / 400 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (171 / 200 : ℚ) (343 / 400 : ℚ) (51 / 1504 : ℚ) (13 / 376 : ℚ) (137 / 160 : ℚ) node_1433 node_1434
theorem node_1431 : Covered ((171 / 200 : ℚ),(343 / 400 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1430 : Covered ((171 / 200 : ℚ),(343 / 400 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (171 / 200 : ℚ) (343 / 400 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1431 node_1432
theorem node_1429 : Covered ((171 / 200 : ℚ),(43 / 50 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (171 / 200 : ℚ) (43 / 50 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (343 / 400 : ℚ) node_1430 node_1437
theorem node_1428 : Covered ((171 / 200 : ℚ),(43 / 50 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1427 : Covered ((171 / 200 : ℚ),(43 / 50 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (171 / 200 : ℚ) (43 / 50 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (25 / 752 : ℚ) node_1428 node_1429
theorem node_1426 : Covered ((341 / 400 : ℚ),(171 / 200 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1425 : Covered ((341 / 400 : ℚ),(171 / 200 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1424 : Covered ((341 / 400 : ℚ),(171 / 200 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (341 / 400 : ℚ) (171 / 200 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1425 node_1426
theorem node_1423 : Covered ((17 / 20 : ℚ),(341 / 400 : ℚ)) ((51 / 1504 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1422 : Covered ((17 / 20 : ℚ),(341 / 400 : ℚ)) ((25 / 752 : ℚ),(51 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1421 : Covered ((17 / 20 : ℚ),(341 / 400 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (341 / 400 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (51 / 1504 : ℚ) node_1422 node_1423
theorem node_1420 : Covered ((17 / 20 : ℚ),(171 / 200 : ℚ)) ((25 / 752 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (171 / 200 : ℚ) (25 / 752 : ℚ) (13 / 376 : ℚ) (341 / 400 : ℚ) node_1421 node_1424
theorem node_1419 : Covered ((17 / 20 : ℚ),(171 / 200 : ℚ)) ((3 / 94 : ℚ),(25 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1418 : Covered ((17 / 20 : ℚ),(171 / 200 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (171 / 200 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (25 / 752 : ℚ) node_1419 node_1420
theorem node_1417 : Covered ((17 / 20 : ℚ),(43 / 50 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 exact split_c (17 / 20 : ℚ) (43 / 50 : ℚ) (3 / 94 : ℚ) (13 / 376 : ℚ) (171 / 200 : ℚ) node_1418 node_1427
theorem node_1416 : Covered ((17 / 20 : ℚ),(43 / 50 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (17 / 20 : ℚ) (43 / 50 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (13 / 376 : ℚ) node_1417 node_1448
theorem node_1415 : Covered ((339 / 400 : ℚ),(17 / 20 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1414 : Covered ((169 / 200 : ℚ),(339 / 400 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1413 : Covered ((677 / 800 : ℚ),(339 / 400 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1412 : Covered ((271 / 320 : ℚ),(339 / 400 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1411 : Covered ((2711 / 3200 : ℚ),(339 / 400 : ℚ)) ((433 / 12032 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1410 : Covered ((2711 / 3200 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(433 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1409 : Covered ((2711 / 3200 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 exact split_j (2711 / 3200 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (217 / 6016 : ℚ) (433 / 12032 : ℚ) node_1410 node_1411
theorem node_1408 : Covered ((271 / 320 : ℚ),(2711 / 3200 : ℚ)) ((433 / 12032 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1407 : Covered ((271 / 320 : ℚ),(2711 / 3200 : ℚ)) ((27 / 752 : ℚ),(433 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1406 : Covered ((271 / 320 : ℚ),(2711 / 3200 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 exact split_j (271 / 320 : ℚ) (2711 / 3200 : ℚ) (27 / 752 : ℚ) (217 / 6016 : ℚ) (433 / 12032 : ℚ) node_1407 node_1408
theorem node_1405 : Covered ((271 / 320 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 exact split_c (271 / 320 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (217 / 6016 : ℚ) (2711 / 3200 : ℚ) node_1406 node_1409
theorem node_1404 : Covered ((271 / 320 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (271 / 320 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1405 node_1412
theorem node_1403 : Covered ((677 / 800 : ℚ),(271 / 320 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1402 : Covered ((2709 / 3200 : ℚ),(271 / 320 : ℚ)) ((433 / 12032 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1401 : Covered ((2709 / 3200 : ℚ),(271 / 320 : ℚ)) ((27 / 752 : ℚ),(433 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1400 : Covered ((2709 / 3200 : ℚ),(271 / 320 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 exact split_j (2709 / 3200 : ℚ) (271 / 320 : ℚ) (27 / 752 : ℚ) (217 / 6016 : ℚ) (433 / 12032 : ℚ) node_1401 node_1402
theorem node_1399 : Covered ((677 / 800 : ℚ),(2709 / 3200 : ℚ)) ((433 / 12032 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1398 : Covered ((677 / 800 : ℚ),(2709 / 3200 : ℚ)) ((27 / 752 : ℚ),(433 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1397 : Covered ((677 / 800 : ℚ),(2709 / 3200 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 exact split_j (677 / 800 : ℚ) (2709 / 3200 : ℚ) (27 / 752 : ℚ) (217 / 6016 : ℚ) (433 / 12032 : ℚ) node_1398 node_1399
theorem node_1396 : Covered ((677 / 800 : ℚ),(271 / 320 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 exact split_c (677 / 800 : ℚ) (271 / 320 : ℚ) (27 / 752 : ℚ) (217 / 6016 : ℚ) (2709 / 3200 : ℚ) node_1397 node_1400
theorem node_1395 : Covered ((677 / 800 : ℚ),(271 / 320 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (677 / 800 : ℚ) (271 / 320 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1396 node_1403
theorem node_1394 : Covered ((677 / 800 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (677 / 800 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (271 / 320 : ℚ) node_1395 node_1404
theorem node_1393 : Covered ((677 / 800 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (677 / 800 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_1394 node_1413
theorem node_1392 : Covered ((169 / 200 : ℚ),(677 / 800 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1391 : Covered ((2707 / 3200 : ℚ),(677 / 800 : ℚ)) ((435 / 12032 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1390 : Covered ((2707 / 3200 : ℚ),(677 / 800 : ℚ)) ((217 / 6016 : ℚ),(435 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1389 : Covered ((2707 / 3200 : ℚ),(677 / 800 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (2707 / 3200 : ℚ) (677 / 800 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (435 / 12032 : ℚ) node_1390 node_1391
theorem node_1388 : Covered ((1353 / 1600 : ℚ),(2707 / 3200 : ℚ)) ((435 / 12032 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1387 : Covered ((1353 / 1600 : ℚ),(2707 / 3200 : ℚ)) ((217 / 6016 : ℚ),(435 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1386 : Covered ((1353 / 1600 : ℚ),(2707 / 3200 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (1353 / 1600 : ℚ) (2707 / 3200 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (435 / 12032 : ℚ) node_1387 node_1388
theorem node_1385 : Covered ((1353 / 1600 : ℚ),(677 / 800 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (1353 / 1600 : ℚ) (677 / 800 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (2707 / 3200 : ℚ) node_1386 node_1389
theorem node_1384 : Covered ((1353 / 1600 : ℚ),(677 / 800 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1383 : Covered ((1353 / 1600 : ℚ),(677 / 800 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (1353 / 1600 : ℚ) (677 / 800 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1384 node_1385
theorem node_1382 : Covered ((541 / 640 : ℚ),(1353 / 1600 : ℚ)) ((435 / 12032 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1381 : Covered ((541 / 640 : ℚ),(1353 / 1600 : ℚ)) ((217 / 6016 : ℚ),(435 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1380 : Covered ((541 / 640 : ℚ),(1353 / 1600 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (541 / 640 : ℚ) (1353 / 1600 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (435 / 12032 : ℚ) node_1381 node_1382
theorem node_1379 : Covered ((169 / 200 : ℚ),(541 / 640 : ℚ)) ((435 / 12032 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1378 : Covered ((169 / 200 : ℚ),(541 / 640 : ℚ)) ((217 / 6016 : ℚ),(435 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1377 : Covered ((169 / 200 : ℚ),(541 / 640 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (541 / 640 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (435 / 12032 : ℚ) node_1378 node_1379
theorem node_1376 : Covered ((169 / 200 : ℚ),(1353 / 1600 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (169 / 200 : ℚ) (1353 / 1600 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (541 / 640 : ℚ) node_1377 node_1380
theorem node_1375 : Covered ((169 / 200 : ℚ),(1353 / 1600 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1374 : Covered ((169 / 200 : ℚ),(1353 / 1600 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (1353 / 1600 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1375 node_1376
theorem node_1373 : Covered ((169 / 200 : ℚ),(677 / 800 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (169 / 200 : ℚ) (677 / 800 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (1353 / 1600 : ℚ) node_1374 node_1383
theorem node_1372 : Covered ((169 / 200 : ℚ),(677 / 800 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (677 / 800 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_1373 node_1392
theorem node_1371 : Covered ((169 / 200 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (169 / 200 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (677 / 800 : ℚ) node_1372 node_1393
theorem node_1370 : Covered ((169 / 200 : ℚ),(339 / 400 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (339 / 400 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_1371 node_1414
theorem node_1369 : Covered ((169 / 200 : ℚ),(17 / 20 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (169 / 200 : ℚ) (17 / 20 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (339 / 400 : ℚ) node_1370 node_1415
theorem node_1368 : Covered ((1359 / 1600 : ℚ),(17 / 20 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1367 : Covered ((2719 / 3200 : ℚ),(17 / 20 : ℚ)) ((429 / 12032 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1366 : Covered ((2719 / 3200 : ℚ),(17 / 20 : ℚ)) ((107 / 3008 : ℚ),(429 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1365 : Covered ((2719 / 3200 : ℚ),(17 / 20 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 exact split_j (2719 / 3200 : ℚ) (17 / 20 : ℚ) (107 / 3008 : ℚ) (215 / 6016 : ℚ) (429 / 12032 : ℚ) node_1366 node_1367
theorem node_1364 : Covered ((1359 / 1600 : ℚ),(2719 / 3200 : ℚ)) ((429 / 12032 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1363 : Covered ((1359 / 1600 : ℚ),(2719 / 3200 : ℚ)) ((107 / 3008 : ℚ),(429 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1362 : Covered ((1359 / 1600 : ℚ),(2719 / 3200 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 exact split_j (1359 / 1600 : ℚ) (2719 / 3200 : ℚ) (107 / 3008 : ℚ) (215 / 6016 : ℚ) (429 / 12032 : ℚ) node_1363 node_1364
theorem node_1361 : Covered ((1359 / 1600 : ℚ),(17 / 20 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 exact split_c (1359 / 1600 : ℚ) (17 / 20 : ℚ) (107 / 3008 : ℚ) (215 / 6016 : ℚ) (2719 / 3200 : ℚ) node_1362 node_1365
theorem node_1360 : Covered ((1359 / 1600 : ℚ),(17 / 20 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (1359 / 1600 : ℚ) (17 / 20 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1361 node_1368
theorem node_1359 : Covered ((2717 / 3200 : ℚ),(1359 / 1600 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1358 : Covered ((679 / 800 : ℚ),(2717 / 3200 : ℚ)) ((431 / 12032 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1357 : Covered ((679 / 800 : ℚ),(2717 / 3200 : ℚ)) ((215 / 6016 : ℚ),(431 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1356 : Covered ((679 / 800 : ℚ),(2717 / 3200 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (679 / 800 : ℚ) (2717 / 3200 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (431 / 12032 : ℚ) node_1357 node_1358
theorem node_1355 : Covered ((679 / 800 : ℚ),(1359 / 1600 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (679 / 800 : ℚ) (1359 / 1600 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (2717 / 3200 : ℚ) node_1356 node_1359
theorem node_1354 : Covered ((679 / 800 : ℚ),(1359 / 1600 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1353 : Covered ((679 / 800 : ℚ),(1359 / 1600 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (679 / 800 : ℚ) (1359 / 1600 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1354 node_1355
theorem node_1352 : Covered ((679 / 800 : ℚ),(17 / 20 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (679 / 800 : ℚ) (17 / 20 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (1359 / 1600 : ℚ) node_1353 node_1360
theorem node_1351 : Covered ((1359 / 1600 : ℚ),(17 / 20 : ℚ)) ((213 / 6016 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1350 : Covered ((1359 / 1600 : ℚ),(17 / 20 : ℚ)) ((53 / 1504 : ℚ),(213 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1349 : Covered ((1359 / 1600 : ℚ),(17 / 20 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_j (1359 / 1600 : ℚ) (17 / 20 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (213 / 6016 : ℚ) node_1350 node_1351
theorem node_1348 : Covered ((679 / 800 : ℚ),(1359 / 1600 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1347 : Covered ((679 / 800 : ℚ),(17 / 20 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 exact split_c (679 / 800 : ℚ) (17 / 20 : ℚ) (53 / 1504 : ℚ) (107 / 3008 : ℚ) (1359 / 1600 : ℚ) node_1348 node_1349
theorem node_1346 : Covered ((679 / 800 : ℚ),(17 / 20 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (679 / 800 : ℚ) (17 / 20 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1347 node_1352
theorem node_1345 : Covered ((543 / 640 : ℚ),(679 / 800 : ℚ)) ((431 / 12032 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1344 : Covered ((543 / 640 : ℚ),(679 / 800 : ℚ)) ((215 / 6016 : ℚ),(431 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1343 : Covered ((543 / 640 : ℚ),(679 / 800 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (543 / 640 : ℚ) (679 / 800 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (431 / 12032 : ℚ) node_1344 node_1345
theorem node_1342 : Covered ((1357 / 1600 : ℚ),(543 / 640 : ℚ)) ((431 / 12032 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1341 : Covered ((1357 / 1600 : ℚ),(543 / 640 : ℚ)) ((215 / 6016 : ℚ),(431 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1340 : Covered ((1357 / 1600 : ℚ),(543 / 640 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (1357 / 1600 : ℚ) (543 / 640 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (431 / 12032 : ℚ) node_1341 node_1342
theorem node_1339 : Covered ((1357 / 1600 : ℚ),(679 / 800 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (1357 / 1600 : ℚ) (679 / 800 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (543 / 640 : ℚ) node_1340 node_1343
theorem node_1338 : Covered ((1357 / 1600 : ℚ),(679 / 800 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1337 : Covered ((1357 / 1600 : ℚ),(679 / 800 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (1357 / 1600 : ℚ) (679 / 800 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1338 node_1339
theorem node_1336 : Covered ((2713 / 3200 : ℚ),(1357 / 1600 : ℚ)) ((431 / 12032 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1335 : Covered ((2713 / 3200 : ℚ),(1357 / 1600 : ℚ)) ((215 / 6016 : ℚ),(431 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1334 : Covered ((2713 / 3200 : ℚ),(1357 / 1600 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (2713 / 3200 : ℚ) (1357 / 1600 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (431 / 12032 : ℚ) node_1335 node_1336
theorem node_1333 : Covered ((339 / 400 : ℚ),(2713 / 3200 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1332 : Covered ((339 / 400 : ℚ),(1357 / 1600 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (339 / 400 : ℚ) (1357 / 1600 : ℚ) (215 / 6016 : ℚ) (27 / 752 : ℚ) (2713 / 3200 : ℚ) node_1333 node_1334
theorem node_1331 : Covered ((339 / 400 : ℚ),(1357 / 1600 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1330 : Covered ((339 / 400 : ℚ),(1357 / 1600 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (339 / 400 : ℚ) (1357 / 1600 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1331 node_1332
theorem node_1329 : Covered ((339 / 400 : ℚ),(679 / 800 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (339 / 400 : ℚ) (679 / 800 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (1357 / 1600 : ℚ) node_1330 node_1337
theorem node_1328 : Covered ((339 / 400 : ℚ),(679 / 800 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1327 : Covered ((339 / 400 : ℚ),(679 / 800 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (339 / 400 : ℚ) (679 / 800 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1328 node_1329
theorem node_1326 : Covered ((339 / 400 : ℚ),(17 / 20 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (339 / 400 : ℚ) (17 / 20 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (679 / 800 : ℚ) node_1327 node_1346
theorem node_1325 : Covered ((679 / 800 : ℚ),(17 / 20 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1324 : Covered ((339 / 400 : ℚ),(679 / 800 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1323 : Covered ((339 / 400 : ℚ),(17 / 20 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 exact split_c (339 / 400 : ℚ) (17 / 20 : ℚ) (13 / 376 : ℚ) (53 / 1504 : ℚ) (679 / 800 : ℚ) node_1324 node_1325
theorem node_1322 : Covered ((339 / 400 : ℚ),(17 / 20 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (339 / 400 : ℚ) (17 / 20 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1323 node_1326
theorem node_1321 : Covered ((271 / 320 : ℚ),(339 / 400 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1320 : Covered ((271 / 320 : ℚ),(339 / 400 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1319 : Covered ((271 / 320 : ℚ),(339 / 400 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (271 / 320 : ℚ) (339 / 400 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1320 node_1321
theorem node_1318 : Covered ((677 / 800 : ℚ),(271 / 320 : ℚ)) ((215 / 6016 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1317 : Covered ((677 / 800 : ℚ),(271 / 320 : ℚ)) ((107 / 3008 : ℚ),(215 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1316 : Covered ((677 / 800 : ℚ),(271 / 320 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (677 / 800 : ℚ) (271 / 320 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (215 / 6016 : ℚ) node_1317 node_1318
theorem node_1315 : Covered ((677 / 800 : ℚ),(339 / 400 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (677 / 800 : ℚ) (339 / 400 : ℚ) (107 / 3008 : ℚ) (27 / 752 : ℚ) (271 / 320 : ℚ) node_1316 node_1319
theorem node_1314 : Covered ((677 / 800 : ℚ),(339 / 400 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1313 : Covered ((677 / 800 : ℚ),(339 / 400 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (677 / 800 : ℚ) (339 / 400 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1314 node_1315
theorem node_1312 : Covered ((169 / 200 : ℚ),(677 / 800 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1311 : Covered ((169 / 200 : ℚ),(677 / 800 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1310 : Covered ((169 / 200 : ℚ),(677 / 800 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (677 / 800 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1311 node_1312
theorem node_1309 : Covered ((169 / 200 : ℚ),(339 / 400 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (169 / 200 : ℚ) (339 / 400 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (677 / 800 : ℚ) node_1310 node_1313
theorem node_1308 : Covered ((169 / 200 : ℚ),(339 / 400 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1307 : Covered ((169 / 200 : ℚ),(339 / 400 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (339 / 400 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1308 node_1309
theorem node_1306 : Covered ((169 / 200 : ℚ),(17 / 20 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (169 / 200 : ℚ) (17 / 20 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (339 / 400 : ℚ) node_1307 node_1322
theorem node_1305 : Covered ((169 / 200 : ℚ),(17 / 20 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (169 / 200 : ℚ) (17 / 20 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_1306 node_1369
theorem node_1304 : Covered ((337 / 400 : ℚ),(169 / 200 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1303 : Covered ((1351 / 1600 : ℚ),(169 / 200 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1302 : Covered ((2703 / 3200 : ℚ),(169 / 200 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1301 : Covered ((1351 / 1600 : ℚ),(2703 / 3200 : ℚ)) ((437 / 12032 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1300 : Covered ((1351 / 1600 : ℚ),(2703 / 3200 : ℚ)) ((109 / 3008 : ℚ),(437 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1299 : Covered ((1351 / 1600 : ℚ),(2703 / 3200 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_j (1351 / 1600 : ℚ) (2703 / 3200 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (437 / 12032 : ℚ) node_1300 node_1301
theorem node_1298 : Covered ((1351 / 1600 : ℚ),(169 / 200 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_c (1351 / 1600 : ℚ) (169 / 200 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (2703 / 3200 : ℚ) node_1299 node_1302
theorem node_1297 : Covered ((1351 / 1600 : ℚ),(169 / 200 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (1351 / 1600 : ℚ) (169 / 200 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1298 node_1303
theorem node_1296 : Covered ((27 / 32 : ℚ),(1351 / 1600 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1295 : Covered ((2701 / 3200 : ℚ),(1351 / 1600 : ℚ)) ((437 / 12032 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1294 : Covered ((2701 / 3200 : ℚ),(1351 / 1600 : ℚ)) ((109 / 3008 : ℚ),(437 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1293 : Covered ((2701 / 3200 : ℚ),(1351 / 1600 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_j (2701 / 3200 : ℚ) (1351 / 1600 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (437 / 12032 : ℚ) node_1294 node_1295
theorem node_1292 : Covered ((27 / 32 : ℚ),(2701 / 3200 : ℚ)) ((437 / 12032 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1291 : Covered ((27 / 32 : ℚ),(2701 / 3200 : ℚ)) ((109 / 3008 : ℚ),(437 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1290 : Covered ((27 / 32 : ℚ),(2701 / 3200 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_j (27 / 32 : ℚ) (2701 / 3200 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (437 / 12032 : ℚ) node_1291 node_1292
theorem node_1289 : Covered ((27 / 32 : ℚ),(1351 / 1600 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_c (27 / 32 : ℚ) (1351 / 1600 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (2701 / 3200 : ℚ) node_1290 node_1293
theorem node_1288 : Covered ((27 / 32 : ℚ),(1351 / 1600 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (27 / 32 : ℚ) (1351 / 1600 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1289 node_1296
theorem node_1287 : Covered ((27 / 32 : ℚ),(169 / 200 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (27 / 32 : ℚ) (169 / 200 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (1351 / 1600 : ℚ) node_1288 node_1297
theorem node_1286 : Covered ((2703 / 3200 : ℚ),(169 / 200 : ℚ)) ((435 / 12032 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1285 : Covered ((2703 / 3200 : ℚ),(169 / 200 : ℚ)) ((217 / 6016 : ℚ),(435 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1284 : Covered ((2703 / 3200 : ℚ),(169 / 200 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (2703 / 3200 : ℚ) (169 / 200 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (435 / 12032 : ℚ) node_1285 node_1286
theorem node_1283 : Covered ((1351 / 1600 : ℚ),(2703 / 3200 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1282 : Covered ((1351 / 1600 : ℚ),(169 / 200 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (1351 / 1600 : ℚ) (169 / 200 : ℚ) (217 / 6016 : ℚ) (109 / 3008 : ℚ) (2703 / 3200 : ℚ) node_1283 node_1284
theorem node_1281 : Covered ((1351 / 1600 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1280 : Covered ((1351 / 1600 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (1351 / 1600 : ℚ) (169 / 200 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1281 node_1282
theorem node_1279 : Covered ((27 / 32 : ℚ),(1351 / 1600 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1278 : Covered ((27 / 32 : ℚ),(1351 / 1600 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1277 : Covered ((27 / 32 : ℚ),(1351 / 1600 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (27 / 32 : ℚ) (1351 / 1600 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1278 node_1279
theorem node_1276 : Covered ((27 / 32 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (27 / 32 : ℚ) (169 / 200 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (1351 / 1600 : ℚ) node_1277 node_1280
theorem node_1275 : Covered ((27 / 32 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (27 / 32 : ℚ) (169 / 200 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_1276 node_1287
theorem node_1274 : Covered ((1349 / 1600 : ℚ),(27 / 32 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1273 : Covered ((2699 / 3200 : ℚ),(27 / 32 : ℚ)) ((437 / 12032 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1272 : Covered ((2699 / 3200 : ℚ),(27 / 32 : ℚ)) ((109 / 3008 : ℚ),(437 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1271 : Covered ((2699 / 3200 : ℚ),(27 / 32 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_j (2699 / 3200 : ℚ) (27 / 32 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (437 / 12032 : ℚ) node_1272 node_1273
theorem node_1270 : Covered ((1349 / 1600 : ℚ),(2699 / 3200 : ℚ)) ((437 / 12032 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1269 : Covered ((1349 / 1600 : ℚ),(2699 / 3200 : ℚ)) ((109 / 3008 : ℚ),(437 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1268 : Covered ((1349 / 1600 : ℚ),(2699 / 3200 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_j (1349 / 1600 : ℚ) (2699 / 3200 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (437 / 12032 : ℚ) node_1269 node_1270
theorem node_1267 : Covered ((1349 / 1600 : ℚ),(27 / 32 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_c (1349 / 1600 : ℚ) (27 / 32 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (2699 / 3200 : ℚ) node_1268 node_1271
theorem node_1266 : Covered ((1349 / 1600 : ℚ),(27 / 32 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (1349 / 1600 : ℚ) (27 / 32 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1267 node_1274
theorem node_1265 : Covered ((2697 / 3200 : ℚ),(1349 / 1600 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1264 : Covered ((2697 / 3200 : ℚ),(1349 / 1600 : ℚ)) ((219 / 6016 : ℚ),(439 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1263 : Covered ((2697 / 3200 : ℚ),(1349 / 1600 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (2697 / 3200 : ℚ) (1349 / 1600 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (439 / 12032 : ℚ) node_1264 node_1265
theorem node_1262 : Covered ((337 / 400 : ℚ),(2697 / 3200 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1261 : Covered ((337 / 400 : ℚ),(2697 / 3200 : ℚ)) ((219 / 6016 : ℚ),(439 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1260 : Covered ((337 / 400 : ℚ),(2697 / 3200 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (337 / 400 : ℚ) (2697 / 3200 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (439 / 12032 : ℚ) node_1261 node_1262
theorem node_1259 : Covered ((337 / 400 : ℚ),(1349 / 1600 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (337 / 400 : ℚ) (1349 / 1600 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (2697 / 3200 : ℚ) node_1260 node_1263
theorem node_1258 : Covered ((2697 / 3200 : ℚ),(1349 / 1600 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1257 : Covered ((337 / 400 : ℚ),(2697 / 3200 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1256 : Covered ((337 / 400 : ℚ),(1349 / 1600 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 exact split_c (337 / 400 : ℚ) (1349 / 1600 : ℚ) (109 / 3008 : ℚ) (219 / 6016 : ℚ) (2697 / 3200 : ℚ) node_1257 node_1258
theorem node_1255 : Covered ((337 / 400 : ℚ),(1349 / 1600 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (337 / 400 : ℚ) (1349 / 1600 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1256 node_1259
theorem node_1254 : Covered ((337 / 400 : ℚ),(27 / 32 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (337 / 400 : ℚ) (27 / 32 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (1349 / 1600 : ℚ) node_1255 node_1266
theorem node_1253 : Covered ((1349 / 1600 : ℚ),(27 / 32 : ℚ)) ((217 / 6016 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1252 : Covered ((1349 / 1600 : ℚ),(27 / 32 : ℚ)) ((27 / 752 : ℚ),(217 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1251 : Covered ((1349 / 1600 : ℚ),(27 / 32 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_j (1349 / 1600 : ℚ) (27 / 32 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (217 / 6016 : ℚ) node_1252 node_1253
theorem node_1250 : Covered ((337 / 400 : ℚ),(1349 / 1600 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1249 : Covered ((337 / 400 : ℚ),(27 / 32 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 exact split_c (337 / 400 : ℚ) (27 / 32 : ℚ) (27 / 752 : ℚ) (109 / 3008 : ℚ) (1349 / 1600 : ℚ) node_1250 node_1251
theorem node_1248 : Covered ((337 / 400 : ℚ),(27 / 32 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (337 / 400 : ℚ) (27 / 32 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_1249 node_1254
theorem node_1247 : Covered ((337 / 400 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (337 / 400 : ℚ) (169 / 200 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (27 / 32 : ℚ) node_1248 node_1275
theorem node_1246 : Covered ((337 / 400 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (337 / 400 : ℚ) (169 / 200 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_1247 node_1304
theorem node_1245 : Covered ((673 / 800 : ℚ),(337 / 400 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1244 : Covered ((1347 / 1600 : ℚ),(337 / 400 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1243 : Covered ((673 / 800 : ℚ),(1347 / 1600 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1242 : Covered ((2693 / 3200 : ℚ),(1347 / 1600 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1241 : Covered ((673 / 800 : ℚ),(2693 / 3200 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1240 : Covered ((673 / 800 : ℚ),(2693 / 3200 : ℚ)) ((55 / 1504 : ℚ),(441 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1239 : Covered ((673 / 800 : ℚ),(2693 / 3200 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_j (673 / 800 : ℚ) (2693 / 3200 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (441 / 12032 : ℚ) node_1240 node_1241
theorem node_1238 : Covered ((673 / 800 : ℚ),(1347 / 1600 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_c (673 / 800 : ℚ) (1347 / 1600 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (2693 / 3200 : ℚ) node_1239 node_1242
theorem node_1237 : Covered ((673 / 800 : ℚ),(1347 / 1600 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (673 / 800 : ℚ) (1347 / 1600 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_1238 node_1243
theorem node_1236 : Covered ((673 / 800 : ℚ),(337 / 400 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (673 / 800 : ℚ) (337 / 400 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (1347 / 1600 : ℚ) node_1237 node_1244
theorem node_1235 : Covered ((673 / 800 : ℚ),(337 / 400 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (673 / 800 : ℚ) (337 / 400 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_1236 node_1245
theorem node_1234 : Covered ((21 / 25 : ℚ),(673 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1233 : Covered ((269 / 320 : ℚ),(673 / 800 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1232 : Covered ((2691 / 3200 : ℚ),(673 / 800 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1231 : Covered ((2691 / 3200 : ℚ),(673 / 800 : ℚ)) ((55 / 1504 : ℚ),(441 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1230 : Covered ((2691 / 3200 : ℚ),(673 / 800 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_j (2691 / 3200 : ℚ) (673 / 800 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (441 / 12032 : ℚ) node_1231 node_1232
theorem node_1229 : Covered ((5381 / 6400 : ℚ),(2691 / 3200 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1228 : Covered ((269 / 320 : ℚ),(5381 / 6400 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1227 : Covered ((269 / 320 : ℚ),(2691 / 3200 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_c (269 / 320 : ℚ) (2691 / 3200 : ℚ) (441 / 12032 : ℚ) (221 / 6016 : ℚ) (5381 / 6400 : ℚ) node_1228 node_1229
theorem node_1226 : Covered ((269 / 320 : ℚ),(2691 / 3200 : ℚ)) ((55 / 1504 : ℚ),(441 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1225 : Covered ((269 / 320 : ℚ),(2691 / 3200 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_j (269 / 320 : ℚ) (2691 / 3200 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (441 / 12032 : ℚ) node_1226 node_1227
theorem node_1224 : Covered ((269 / 320 : ℚ),(673 / 800 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_c (269 / 320 : ℚ) (673 / 800 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (2691 / 3200 : ℚ) node_1225 node_1230
theorem node_1223 : Covered ((269 / 320 : ℚ),(673 / 800 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (269 / 320 : ℚ) (673 / 800 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_1224 node_1233
theorem node_1222 : Covered ((21 / 25 : ℚ),(269 / 320 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1221 : Covered ((2689 / 3200 : ℚ),(269 / 320 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1220 : Covered ((2689 / 3200 : ℚ),(269 / 320 : ℚ)) ((55 / 1504 : ℚ),(441 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1219 : Covered ((2689 / 3200 : ℚ),(269 / 320 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_j (2689 / 3200 : ℚ) (269 / 320 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (441 / 12032 : ℚ) node_1220 node_1221
theorem node_1218 : Covered ((21 / 25 : ℚ),(2689 / 3200 : ℚ)) ((441 / 12032 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1217 : Covered ((21 / 25 : ℚ),(2689 / 3200 : ℚ)) ((55 / 1504 : ℚ),(441 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1216 : Covered ((21 / 25 : ℚ),(2689 / 3200 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (2689 / 3200 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (441 / 12032 : ℚ) node_1217 node_1218
theorem node_1215 : Covered ((21 / 25 : ℚ),(269 / 320 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (269 / 320 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (2689 / 3200 : ℚ) node_1216 node_1219
theorem node_1214 : Covered ((21 / 25 : ℚ),(269 / 320 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (269 / 320 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_1215 node_1222
theorem node_1213 : Covered ((21 / 25 : ℚ),(673 / 800 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (673 / 800 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (269 / 320 : ℚ) node_1214 node_1223
theorem node_1212 : Covered ((21 / 25 : ℚ),(673 / 800 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (673 / 800 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_1213 node_1234
theorem node_1211 : Covered ((21 / 25 : ℚ),(337 / 400 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (337 / 400 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (673 / 800 : ℚ) node_1212 node_1235
theorem node_1210 : Covered ((5391 / 6400 : ℚ),(337 / 400 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1209 : Covered ((539 / 640 : ℚ),(5391 / 6400 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1208 : Covered ((539 / 640 : ℚ),(337 / 400 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (539 / 640 : ℚ) (337 / 400 : ℚ) (439 / 12032 : ℚ) (55 / 1504 : ℚ) (5391 / 6400 : ℚ) node_1209 node_1210
theorem node_1207 : Covered ((539 / 640 : ℚ),(337 / 400 : ℚ)) ((219 / 6016 : ℚ),(439 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1206 : Covered ((539 / 640 : ℚ),(337 / 400 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (539 / 640 : ℚ) (337 / 400 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (439 / 12032 : ℚ) node_1207 node_1208
theorem node_1205 : Covered ((1347 / 1600 : ℚ),(539 / 640 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1204 : Covered ((1347 / 1600 : ℚ),(539 / 640 : ℚ)) ((219 / 6016 : ℚ),(439 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1203 : Covered ((1347 / 1600 : ℚ),(539 / 640 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (1347 / 1600 : ℚ) (539 / 640 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (439 / 12032 : ℚ) node_1204 node_1205
theorem node_1202 : Covered ((1347 / 1600 : ℚ),(337 / 400 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (1347 / 1600 : ℚ) (337 / 400 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (539 / 640 : ℚ) node_1203 node_1206
theorem node_1201 : Covered ((1347 / 1600 : ℚ),(337 / 400 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1200 : Covered ((1347 / 1600 : ℚ),(337 / 400 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (1347 / 1600 : ℚ) (337 / 400 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1201 node_1202
theorem node_1199 : Covered ((2693 / 3200 : ℚ),(1347 / 1600 : ℚ)) ((439 / 12032 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1198 : Covered ((2693 / 3200 : ℚ),(1347 / 1600 : ℚ)) ((219 / 6016 : ℚ),(439 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1197 : Covered ((2693 / 3200 : ℚ),(1347 / 1600 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (2693 / 3200 : ℚ) (1347 / 1600 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (439 / 12032 : ℚ) node_1198 node_1199
theorem node_1196 : Covered ((673 / 800 : ℚ),(2693 / 3200 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1195 : Covered ((673 / 800 : ℚ),(1347 / 1600 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (673 / 800 : ℚ) (1347 / 1600 : ℚ) (219 / 6016 : ℚ) (55 / 1504 : ℚ) (2693 / 3200 : ℚ) node_1196 node_1197
theorem node_1194 : Covered ((673 / 800 : ℚ),(1347 / 1600 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1193 : Covered ((673 / 800 : ℚ),(1347 / 1600 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (673 / 800 : ℚ) (1347 / 1600 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1194 node_1195
theorem node_1192 : Covered ((673 / 800 : ℚ),(337 / 400 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (673 / 800 : ℚ) (337 / 400 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (1347 / 1600 : ℚ) node_1193 node_1200
theorem node_1191 : Covered ((673 / 800 : ℚ),(337 / 400 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1190 : Covered ((673 / 800 : ℚ),(337 / 400 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (673 / 800 : ℚ) (337 / 400 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_1191 node_1192
theorem node_1189 : Covered ((269 / 320 : ℚ),(673 / 800 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1188 : Covered ((269 / 320 : ℚ),(673 / 800 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1187 : Covered ((269 / 320 : ℚ),(673 / 800 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (269 / 320 : ℚ) (673 / 800 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1188 node_1189
theorem node_1186 : Covered ((21 / 25 : ℚ),(269 / 320 : ℚ)) ((219 / 6016 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1185 : Covered ((21 / 25 : ℚ),(269 / 320 : ℚ)) ((109 / 3008 : ℚ),(219 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1184 : Covered ((21 / 25 : ℚ),(269 / 320 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (269 / 320 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (219 / 6016 : ℚ) node_1185 node_1186
theorem node_1183 : Covered ((21 / 25 : ℚ),(673 / 800 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (673 / 800 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (269 / 320 : ℚ) node_1184 node_1187
theorem node_1182 : Covered ((21 / 25 : ℚ),(673 / 800 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1181 : Covered ((21 / 25 : ℚ),(673 / 800 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (673 / 800 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_1182 node_1183
theorem node_1180 : Covered ((21 / 25 : ℚ),(337 / 400 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (337 / 400 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (673 / 800 : ℚ) node_1181 node_1190
theorem node_1179 : Covered ((21 / 25 : ℚ),(337 / 400 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (337 / 400 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_1180 node_1211
theorem node_1178 : Covered ((21 / 25 : ℚ),(169 / 200 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (169 / 200 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (337 / 400 : ℚ) node_1179 node_1246
theorem node_1177 : Covered ((27 / 32 : ℚ),(169 / 200 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1176 : Covered ((27 / 32 : ℚ),(169 / 200 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1175 : Covered ((27 / 32 : ℚ),(169 / 200 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (27 / 32 : ℚ) (169 / 200 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1176 node_1177
theorem node_1174 : Covered ((337 / 400 : ℚ),(27 / 32 : ℚ)) ((107 / 3008 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1173 : Covered ((337 / 400 : ℚ),(27 / 32 : ℚ)) ((53 / 1504 : ℚ),(107 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1172 : Covered ((337 / 400 : ℚ),(27 / 32 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (337 / 400 : ℚ) (27 / 32 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (107 / 3008 : ℚ) node_1173 node_1174
theorem node_1171 : Covered ((337 / 400 : ℚ),(169 / 200 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (337 / 400 : ℚ) (169 / 200 : ℚ) (53 / 1504 : ℚ) (27 / 752 : ℚ) (27 / 32 : ℚ) node_1172 node_1175
theorem node_1170 : Covered ((337 / 400 : ℚ),(169 / 200 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1169 : Covered ((337 / 400 : ℚ),(169 / 200 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (337 / 400 : ℚ) (169 / 200 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1170 node_1171
theorem node_1168 : Covered ((21 / 25 : ℚ),(337 / 400 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1167 : Covered ((21 / 25 : ℚ),(337 / 400 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1166 : Covered ((21 / 25 : ℚ),(337 / 400 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (337 / 400 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_1167 node_1168
theorem node_1165 : Covered ((21 / 25 : ℚ),(169 / 200 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (169 / 200 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (337 / 400 : ℚ) node_1166 node_1169
theorem node_1164 : Covered ((21 / 25 : ℚ),(169 / 200 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (169 / 200 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_1165 node_1178
theorem node_1163 : Covered ((21 / 25 : ℚ),(17 / 20 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (17 / 20 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (169 / 200 : ℚ) node_1164 node_1305
theorem node_1162 : Covered ((21 / 25 : ℚ),(17 / 20 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1161 : Covered ((21 / 25 : ℚ),(17 / 20 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (17 / 20 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (13 / 376 : ℚ) node_1162 node_1163
theorem node_1160 : Covered ((21 / 25 : ℚ),(43 / 50 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (43 / 50 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (17 / 20 : ℚ) node_1161 node_1416
theorem node_1159 : Covered ((21 / 25 : ℚ),(43 / 50 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (43 / 50 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_1160 node_1597
theorem node_1158 : Covered ((21 / 25 : ℚ),(22 / 25 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (21 / 25 : ℚ) (22 / 25 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (43 / 50 : ℚ) node_1159 node_1598
theorem node_1157 : Covered ((21 / 25 : ℚ),(22 / 25 : ℚ)) ((1 / 47 : ℚ),(3 / 94 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1156 : Covered ((21 / 25 : ℚ),(22 / 25 : ℚ)) ((1 / 47 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (21 / 25 : ℚ) (22 / 25 : ℚ) (1 / 47 : ℚ) (2 / 47 : ℚ) (3 / 94 : ℚ) node_1157 node_1158
theorem node_1155 : Covered ((83 / 100 : ℚ),(21 / 25 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1154 : Covered ((167 / 200 : ℚ),(21 / 25 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1153 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1152 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1151 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1150 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1149 : Covered ((1337 / 1600 : ℚ),(669 / 800 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1148 : Covered ((167 / 200 : ℚ),(1337 / 1600 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1147 : Covered ((2673 / 3200 : ℚ),(1337 / 1600 : ℚ)) ((449 / 12032 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1146 : Covered ((5347 / 6400 : ℚ),(1337 / 1600 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1145 : Covered ((2673 / 3200 : ℚ),(5347 / 6400 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1144 : Covered ((2673 / 3200 : ℚ),(1337 / 1600 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 exact split_c (2673 / 3200 : ℚ) (1337 / 1600 : ℚ) (7 / 188 : ℚ) (449 / 12032 : ℚ) (5347 / 6400 : ℚ) node_1145 node_1146
theorem node_1143 : Covered ((2673 / 3200 : ℚ),(1337 / 1600 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_j (2673 / 3200 : ℚ) (1337 / 1600 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (449 / 12032 : ℚ) node_1144 node_1147
theorem node_1142 : Covered ((167 / 200 : ℚ),(2673 / 3200 : ℚ)) ((449 / 12032 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1141 : Covered ((167 / 200 : ℚ),(2673 / 3200 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1140 : Covered ((167 / 200 : ℚ),(2673 / 3200 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (2673 / 3200 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (449 / 12032 : ℚ) node_1141 node_1142
theorem node_1139 : Covered ((167 / 200 : ℚ),(1337 / 1600 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (1337 / 1600 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (2673 / 3200 : ℚ) node_1140 node_1143
theorem node_1138 : Covered ((167 / 200 : ℚ),(1337 / 1600 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (1337 / 1600 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1139 node_1148
theorem node_1137 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (669 / 800 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (1337 / 1600 : ℚ) node_1138 node_1149
theorem node_1136 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (669 / 800 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_1137 node_1150
theorem node_1135 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (67 / 80 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (669 / 800 : ℚ) node_1136 node_1151
theorem node_1134 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (67 / 80 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_1135 node_1152
theorem node_1133 : Covered ((167 / 200 : ℚ),(21 / 25 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (21 / 25 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (67 / 80 : ℚ) node_1134 node_1153
theorem node_1132 : Covered ((167 / 200 : ℚ),(21 / 25 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (21 / 25 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_1133 node_1154
theorem node_1131 : Covered ((83 / 100 : ℚ),(167 / 200 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1130 : Covered ((333 / 400 : ℚ),(167 / 200 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1129 : Covered ((667 / 800 : ℚ),(167 / 200 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1128 : Covered ((267 / 320 : ℚ),(167 / 200 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1127 : Covered ((2671 / 3200 : ℚ),(167 / 200 : ℚ)) ((449 / 12032 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1126 : Covered ((2671 / 3200 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1125 : Covered ((2671 / 3200 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_j (2671 / 3200 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (449 / 12032 : ℚ) node_1126 node_1127
theorem node_1124 : Covered ((267 / 320 : ℚ),(2671 / 3200 : ℚ)) ((449 / 12032 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1123 : Covered ((267 / 320 : ℚ),(2671 / 3200 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1122 : Covered ((267 / 320 : ℚ),(2671 / 3200 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_j (267 / 320 : ℚ) (2671 / 3200 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (449 / 12032 : ℚ) node_1123 node_1124
theorem node_1121 : Covered ((267 / 320 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_c (267 / 320 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (2671 / 3200 : ℚ) node_1122 node_1125
theorem node_1120 : Covered ((267 / 320 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (267 / 320 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1121 node_1128
theorem node_1119 : Covered ((2669 / 3200 : ℚ),(267 / 320 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1118 : Covered ((667 / 800 : ℚ),(2669 / 3200 : ℚ)) ((451 / 12032 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1117 : Covered ((5337 / 6400 : ℚ),(2669 / 3200 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1116 : Covered ((667 / 800 : ℚ),(5337 / 6400 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1115 : Covered ((667 / 800 : ℚ),(2669 / 3200 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 exact split_c (667 / 800 : ℚ) (2669 / 3200 : ℚ) (225 / 6016 : ℚ) (451 / 12032 : ℚ) (5337 / 6400 : ℚ) node_1116 node_1117
theorem node_1114 : Covered ((667 / 800 : ℚ),(2669 / 3200 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (667 / 800 : ℚ) (2669 / 3200 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (451 / 12032 : ℚ) node_1115 node_1118
theorem node_1113 : Covered ((667 / 800 : ℚ),(267 / 320 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (667 / 800 : ℚ) (267 / 320 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (2669 / 3200 : ℚ) node_1114 node_1119
theorem node_1112 : Covered ((2669 / 3200 : ℚ),(267 / 320 : ℚ)) ((449 / 12032 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1111 : Covered ((2669 / 3200 : ℚ),(267 / 320 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1110 : Covered ((2669 / 3200 : ℚ),(267 / 320 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_j (2669 / 3200 : ℚ) (267 / 320 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (449 / 12032 : ℚ) node_1111 node_1112
theorem node_1109 : Covered ((667 / 800 : ℚ),(2669 / 3200 : ℚ)) ((449 / 12032 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1108 : Covered ((667 / 800 : ℚ),(2669 / 3200 : ℚ)) ((7 / 188 : ℚ),(449 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1107 : Covered ((667 / 800 : ℚ),(2669 / 3200 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_j (667 / 800 : ℚ) (2669 / 3200 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (449 / 12032 : ℚ) node_1108 node_1109
theorem node_1106 : Covered ((667 / 800 : ℚ),(267 / 320 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 exact split_c (667 / 800 : ℚ) (267 / 320 : ℚ) (7 / 188 : ℚ) (225 / 6016 : ℚ) (2669 / 3200 : ℚ) node_1107 node_1110
theorem node_1105 : Covered ((667 / 800 : ℚ),(267 / 320 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (667 / 800 : ℚ) (267 / 320 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1106 node_1113
theorem node_1104 : Covered ((667 / 800 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (667 / 800 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (267 / 320 : ℚ) node_1105 node_1120
theorem node_1103 : Covered ((667 / 800 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (667 / 800 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_1104 node_1129
theorem node_1102 : Covered ((333 / 400 : ℚ),(667 / 800 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1101 : Covered ((2667 / 3200 : ℚ),(667 / 800 : ℚ)) ((451 / 12032 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1100 : Covered ((2667 / 3200 : ℚ),(667 / 800 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1099 : Covered ((2667 / 3200 : ℚ),(667 / 800 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (2667 / 3200 : ℚ) (667 / 800 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (451 / 12032 : ℚ) node_1100 node_1101
theorem node_1098 : Covered ((1333 / 1600 : ℚ),(2667 / 3200 : ℚ)) ((451 / 12032 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1097 : Covered ((1333 / 1600 : ℚ),(2667 / 3200 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1096 : Covered ((1333 / 1600 : ℚ),(2667 / 3200 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (1333 / 1600 : ℚ) (2667 / 3200 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (451 / 12032 : ℚ) node_1097 node_1098
theorem node_1095 : Covered ((1333 / 1600 : ℚ),(667 / 800 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (1333 / 1600 : ℚ) (667 / 800 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (2667 / 3200 : ℚ) node_1096 node_1099
theorem node_1094 : Covered ((1333 / 1600 : ℚ),(667 / 800 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1093 : Covered ((1333 / 1600 : ℚ),(667 / 800 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (1333 / 1600 : ℚ) (667 / 800 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1094 node_1095
theorem node_1092 : Covered ((533 / 640 : ℚ),(1333 / 1600 : ℚ)) ((451 / 12032 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1091 : Covered ((533 / 640 : ℚ),(1333 / 1600 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1090 : Covered ((533 / 640 : ℚ),(1333 / 1600 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (533 / 640 : ℚ) (1333 / 1600 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (451 / 12032 : ℚ) node_1091 node_1092
theorem node_1089 : Covered ((333 / 400 : ℚ),(533 / 640 : ℚ)) ((451 / 12032 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1088 : Covered ((333 / 400 : ℚ),(533 / 640 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1087 : Covered ((333 / 400 : ℚ),(533 / 640 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (333 / 400 : ℚ) (533 / 640 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (451 / 12032 : ℚ) node_1088 node_1089
theorem node_1086 : Covered ((333 / 400 : ℚ),(1333 / 1600 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (333 / 400 : ℚ) (1333 / 1600 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (533 / 640 : ℚ) node_1087 node_1090
theorem node_1085 : Covered ((333 / 400 : ℚ),(1333 / 1600 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1084 : Covered ((333 / 400 : ℚ),(1333 / 1600 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (333 / 400 : ℚ) (1333 / 1600 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1085 node_1086
theorem node_1083 : Covered ((333 / 400 : ℚ),(667 / 800 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (333 / 400 : ℚ) (667 / 800 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (1333 / 1600 : ℚ) node_1084 node_1093
theorem node_1082 : Covered ((333 / 400 : ℚ),(667 / 800 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (333 / 400 : ℚ) (667 / 800 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_1083 node_1102
theorem node_1081 : Covered ((333 / 400 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (333 / 400 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (667 / 800 : ℚ) node_1082 node_1103
theorem node_1080 : Covered ((333 / 400 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (333 / 400 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_1081 node_1130
theorem node_1079 : Covered ((83 / 100 : ℚ),(333 / 400 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1078 : Covered ((1331 / 1600 : ℚ),(333 / 400 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1077 : Covered ((2663 / 3200 : ℚ),(333 / 400 : ℚ)) ((453 / 12032 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1076 : Covered ((5327 / 6400 : ℚ),(333 / 400 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1075 : Covered ((2663 / 3200 : ℚ),(5327 / 6400 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1074 : Covered ((2663 / 3200 : ℚ),(333 / 400 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 exact split_c (2663 / 3200 : ℚ) (333 / 400 : ℚ) (113 / 3008 : ℚ) (453 / 12032 : ℚ) (5327 / 6400 : ℚ) node_1075 node_1076
theorem node_1073 : Covered ((2663 / 3200 : ℚ),(333 / 400 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_j (2663 / 3200 : ℚ) (333 / 400 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (453 / 12032 : ℚ) node_1074 node_1077
theorem node_1072 : Covered ((1331 / 1600 : ℚ),(2663 / 3200 : ℚ)) ((453 / 12032 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1071 : Covered ((1331 / 1600 : ℚ),(2663 / 3200 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1070 : Covered ((1331 / 1600 : ℚ),(2663 / 3200 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_j (1331 / 1600 : ℚ) (2663 / 3200 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (453 / 12032 : ℚ) node_1071 node_1072
theorem node_1069 : Covered ((1331 / 1600 : ℚ),(333 / 400 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_c (1331 / 1600 : ℚ) (333 / 400 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (2663 / 3200 : ℚ) node_1070 node_1073
theorem node_1068 : Covered ((1331 / 1600 : ℚ),(333 / 400 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (1331 / 1600 : ℚ) (333 / 400 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_1069 node_1078
theorem node_1067 : Covered ((133 / 160 : ℚ),(1331 / 1600 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1066 : Covered ((2661 / 3200 : ℚ),(1331 / 1600 : ℚ)) ((453 / 12032 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1065 : Covered ((2661 / 3200 : ℚ),(1331 / 1600 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1064 : Covered ((2661 / 3200 : ℚ),(1331 / 1600 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_j (2661 / 3200 : ℚ) (1331 / 1600 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (453 / 12032 : ℚ) node_1065 node_1066
theorem node_1063 : Covered ((133 / 160 : ℚ),(2661 / 3200 : ℚ)) ((453 / 12032 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1062 : Covered ((133 / 160 : ℚ),(2661 / 3200 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1061 : Covered ((133 / 160 : ℚ),(2661 / 3200 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_j (133 / 160 : ℚ) (2661 / 3200 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (453 / 12032 : ℚ) node_1062 node_1063
theorem node_1060 : Covered ((133 / 160 : ℚ),(1331 / 1600 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_c (133 / 160 : ℚ) (1331 / 1600 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (2661 / 3200 : ℚ) node_1061 node_1064
theorem node_1059 : Covered ((133 / 160 : ℚ),(1331 / 1600 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (133 / 160 : ℚ) (1331 / 1600 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_1060 node_1067
theorem node_1058 : Covered ((133 / 160 : ℚ),(333 / 400 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (133 / 160 : ℚ) (333 / 400 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (1331 / 1600 : ℚ) node_1059 node_1068
theorem node_1057 : Covered ((2663 / 3200 : ℚ),(333 / 400 : ℚ)) ((451 / 12032 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1056 : Covered ((2663 / 3200 : ℚ),(333 / 400 : ℚ)) ((225 / 6016 : ℚ),(451 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1055 : Covered ((2663 / 3200 : ℚ),(333 / 400 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (2663 / 3200 : ℚ) (333 / 400 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (451 / 12032 : ℚ) node_1056 node_1057
theorem node_1054 : Covered ((1331 / 1600 : ℚ),(2663 / 3200 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1053 : Covered ((1331 / 1600 : ℚ),(333 / 400 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (1331 / 1600 : ℚ) (333 / 400 : ℚ) (225 / 6016 : ℚ) (113 / 3008 : ℚ) (2663 / 3200 : ℚ) node_1054 node_1055
theorem node_1052 : Covered ((1331 / 1600 : ℚ),(333 / 400 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1051 : Covered ((1331 / 1600 : ℚ),(333 / 400 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (1331 / 1600 : ℚ) (333 / 400 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1052 node_1053
theorem node_1050 : Covered ((133 / 160 : ℚ),(1331 / 1600 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1049 : Covered ((133 / 160 : ℚ),(1331 / 1600 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1048 : Covered ((133 / 160 : ℚ),(1331 / 1600 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (133 / 160 : ℚ) (1331 / 1600 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1049 node_1050
theorem node_1047 : Covered ((133 / 160 : ℚ),(333 / 400 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (133 / 160 : ℚ) (333 / 400 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (1331 / 1600 : ℚ) node_1048 node_1051
theorem node_1046 : Covered ((133 / 160 : ℚ),(333 / 400 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (133 / 160 : ℚ) (333 / 400 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_1047 node_1058
theorem node_1045 : Covered ((2659 / 3200 : ℚ),(133 / 160 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1044 : Covered ((1329 / 1600 : ℚ),(2659 / 3200 : ℚ)) ((455 / 12032 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1043 : Covered ((1329 / 1600 : ℚ),(2659 / 3200 : ℚ)) ((227 / 6016 : ℚ),(455 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1042 : Covered ((1329 / 1600 : ℚ),(2659 / 3200 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (1329 / 1600 : ℚ) (2659 / 3200 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (455 / 12032 : ℚ) node_1043 node_1044
theorem node_1041 : Covered ((1329 / 1600 : ℚ),(133 / 160 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (1329 / 1600 : ℚ) (133 / 160 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (2659 / 3200 : ℚ) node_1042 node_1045
theorem node_1040 : Covered ((2659 / 3200 : ℚ),(133 / 160 : ℚ)) ((453 / 12032 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1039 : Covered ((2659 / 3200 : ℚ),(133 / 160 : ℚ)) ((113 / 3008 : ℚ),(453 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1038 : Covered ((2659 / 3200 : ℚ),(133 / 160 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_j (2659 / 3200 : ℚ) (133 / 160 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (453 / 12032 : ℚ) node_1039 node_1040
theorem node_1037 : Covered ((1329 / 1600 : ℚ),(2659 / 3200 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1036 : Covered ((1329 / 1600 : ℚ),(133 / 160 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 exact split_c (1329 / 1600 : ℚ) (133 / 160 : ℚ) (113 / 3008 : ℚ) (227 / 6016 : ℚ) (2659 / 3200 : ℚ) node_1037 node_1038
theorem node_1035 : Covered ((1329 / 1600 : ℚ),(133 / 160 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (1329 / 1600 : ℚ) (133 / 160 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_1036 node_1041
theorem node_1034 : Covered ((2657 / 3200 : ℚ),(1329 / 1600 : ℚ)) ((455 / 12032 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1033 : Covered ((2657 / 3200 : ℚ),(1329 / 1600 : ℚ)) ((227 / 6016 : ℚ),(455 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1032 : Covered ((2657 / 3200 : ℚ),(1329 / 1600 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (2657 / 3200 : ℚ) (1329 / 1600 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (455 / 12032 : ℚ) node_1033 node_1034
theorem node_1031 : Covered ((83 / 100 : ℚ),(2657 / 3200 : ℚ)) ((455 / 12032 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1030 : Covered ((83 / 100 : ℚ),(2657 / 3200 : ℚ)) ((227 / 6016 : ℚ),(455 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1029 : Covered ((83 / 100 : ℚ),(2657 / 3200 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (2657 / 3200 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (455 / 12032 : ℚ) node_1030 node_1031
theorem node_1028 : Covered ((83 / 100 : ℚ),(1329 / 1600 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (1329 / 1600 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (2657 / 3200 : ℚ) node_1029 node_1032
theorem node_1027 : Covered ((83 / 100 : ℚ),(1329 / 1600 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1026 : Covered ((83 / 100 : ℚ),(1329 / 1600 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (1329 / 1600 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_1027 node_1028
theorem node_1025 : Covered ((83 / 100 : ℚ),(133 / 160 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (133 / 160 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (1329 / 1600 : ℚ) node_1026 node_1035
theorem node_1024 : Covered ((1329 / 1600 : ℚ),(133 / 160 : ℚ)) ((225 / 6016 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1023 : Covered ((1329 / 1600 : ℚ),(133 / 160 : ℚ)) ((7 / 188 : ℚ),(225 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1022 : Covered ((1329 / 1600 : ℚ),(133 / 160 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_j (1329 / 1600 : ℚ) (133 / 160 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (225 / 6016 : ℚ) node_1023 node_1024
theorem node_1021 : Covered ((83 / 100 : ℚ),(1329 / 1600 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1020 : Covered ((83 / 100 : ℚ),(133 / 160 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (133 / 160 : ℚ) (7 / 188 : ℚ) (113 / 3008 : ℚ) (1329 / 1600 : ℚ) node_1021 node_1022
theorem node_1019 : Covered ((83 / 100 : ℚ),(133 / 160 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (133 / 160 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_1020 node_1025
theorem node_1018 : Covered ((83 / 100 : ℚ),(333 / 400 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (333 / 400 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (133 / 160 : ℚ) node_1019 node_1046
theorem node_1017 : Covered ((83 / 100 : ℚ),(333 / 400 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (333 / 400 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_1018 node_1079
theorem node_1016 : Covered ((83 / 100 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (333 / 400 : ℚ) node_1017 node_1080
theorem node_1015 : Covered ((83 / 100 : ℚ),(167 / 200 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (167 / 200 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_1016 node_1131
theorem node_1014 : Covered ((83 / 100 : ℚ),(21 / 25 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (21 / 25 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (167 / 200 : ℚ) node_1015 node_1132
theorem node_1013 : Covered ((83 / 100 : ℚ),(21 / 25 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (21 / 25 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_1014 node_1155
theorem node_1012 : Covered ((41 / 50 : ℚ),(83 / 100 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1011 : Covered ((33 / 40 : ℚ),(83 / 100 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1010 : Covered ((663 / 800 : ℚ),(83 / 100 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1009 : Covered ((1327 / 1600 : ℚ),(83 / 100 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1008 : Covered ((663 / 800 : ℚ),(1327 / 1600 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1007 : Covered ((2653 / 3200 : ℚ),(1327 / 1600 : ℚ)) ((457 / 12032 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1006 : Covered ((2653 / 3200 : ℚ),(1327 / 1600 : ℚ)) ((57 / 1504 : ℚ),(457 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1005 : Covered ((2653 / 3200 : ℚ),(1327 / 1600 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_j (2653 / 3200 : ℚ) (1327 / 1600 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (457 / 12032 : ℚ) node_1006 node_1007
theorem node_1004 : Covered ((663 / 800 : ℚ),(2653 / 3200 : ℚ)) ((457 / 12032 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1003 : Covered ((663 / 800 : ℚ),(2653 / 3200 : ℚ)) ((57 / 1504 : ℚ),(457 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_1002 : Covered ((663 / 800 : ℚ),(2653 / 3200 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_j (663 / 800 : ℚ) (2653 / 3200 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (457 / 12032 : ℚ) node_1003 node_1004
theorem node_1001 : Covered ((663 / 800 : ℚ),(1327 / 1600 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_c (663 / 800 : ℚ) (1327 / 1600 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (2653 / 3200 : ℚ) node_1002 node_1005
theorem node_1000 : Covered ((663 / 800 : ℚ),(1327 / 1600 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (663 / 800 : ℚ) (1327 / 1600 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_1001 node_1008
theorem node_999 : Covered ((663 / 800 : ℚ),(83 / 100 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (663 / 800 : ℚ) (83 / 100 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (1327 / 1600 : ℚ) node_1000 node_1009
theorem node_998 : Covered ((663 / 800 : ℚ),(83 / 100 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (663 / 800 : ℚ) (83 / 100 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_999 node_1010
theorem node_997 : Covered ((331 / 400 : ℚ),(663 / 800 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_996 : Covered ((53 / 64 : ℚ),(663 / 800 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_995 : Covered ((2651 / 3200 : ℚ),(663 / 800 : ℚ)) ((457 / 12032 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_994 : Covered ((2651 / 3200 : ℚ),(663 / 800 : ℚ)) ((57 / 1504 : ℚ),(457 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_993 : Covered ((2651 / 3200 : ℚ),(663 / 800 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_j (2651 / 3200 : ℚ) (663 / 800 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (457 / 12032 : ℚ) node_994 node_995
theorem node_992 : Covered ((53 / 64 : ℚ),(2651 / 3200 : ℚ)) ((457 / 12032 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_991 : Covered ((53 / 64 : ℚ),(2651 / 3200 : ℚ)) ((57 / 1504 : ℚ),(457 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_990 : Covered ((53 / 64 : ℚ),(2651 / 3200 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_j (53 / 64 : ℚ) (2651 / 3200 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (457 / 12032 : ℚ) node_991 node_992
theorem node_989 : Covered ((53 / 64 : ℚ),(663 / 800 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_c (53 / 64 : ℚ) (663 / 800 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (2651 / 3200 : ℚ) node_990 node_993
theorem node_988 : Covered ((53 / 64 : ℚ),(663 / 800 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (53 / 64 : ℚ) (663 / 800 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_989 node_996
theorem node_987 : Covered ((2649 / 3200 : ℚ),(53 / 64 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_986 : Covered ((331 / 400 : ℚ),(2649 / 3200 : ℚ)) ((459 / 12032 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_985 : Covered ((331 / 400 : ℚ),(2649 / 3200 : ℚ)) ((229 / 6016 : ℚ),(459 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_984 : Covered ((331 / 400 : ℚ),(2649 / 3200 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (2649 / 3200 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (459 / 12032 : ℚ) node_985 node_986
theorem node_983 : Covered ((331 / 400 : ℚ),(53 / 64 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (331 / 400 : ℚ) (53 / 64 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (2649 / 3200 : ℚ) node_984 node_987
theorem node_982 : Covered ((2649 / 3200 : ℚ),(53 / 64 : ℚ)) ((457 / 12032 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_981 : Covered ((2649 / 3200 : ℚ),(53 / 64 : ℚ)) ((57 / 1504 : ℚ),(457 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_980 : Covered ((2649 / 3200 : ℚ),(53 / 64 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_j (2649 / 3200 : ℚ) (53 / 64 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (457 / 12032 : ℚ) node_981 node_982
theorem node_979 : Covered ((331 / 400 : ℚ),(2649 / 3200 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_978 : Covered ((331 / 400 : ℚ),(53 / 64 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 exact split_c (331 / 400 : ℚ) (53 / 64 : ℚ) (57 / 1504 : ℚ) (229 / 6016 : ℚ) (2649 / 3200 : ℚ) node_979 node_980
theorem node_977 : Covered ((331 / 400 : ℚ),(53 / 64 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (53 / 64 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_978 node_983
theorem node_976 : Covered ((331 / 400 : ℚ),(663 / 800 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (331 / 400 : ℚ) (663 / 800 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (53 / 64 : ℚ) node_977 node_988
theorem node_975 : Covered ((331 / 400 : ℚ),(663 / 800 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (663 / 800 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_976 node_997
theorem node_974 : Covered ((331 / 400 : ℚ),(83 / 100 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (331 / 400 : ℚ) (83 / 100 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (663 / 800 : ℚ) node_975 node_998
theorem node_973 : Covered ((531 / 640 : ℚ),(83 / 100 : ℚ)) ((455 / 12032 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_972 : Covered ((531 / 640 : ℚ),(83 / 100 : ℚ)) ((227 / 6016 : ℚ),(455 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_971 : Covered ((531 / 640 : ℚ),(83 / 100 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (531 / 640 : ℚ) (83 / 100 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (455 / 12032 : ℚ) node_972 node_973
theorem node_970 : Covered ((1327 / 1600 : ℚ),(531 / 640 : ℚ)) ((455 / 12032 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_969 : Covered ((1327 / 1600 : ℚ),(531 / 640 : ℚ)) ((227 / 6016 : ℚ),(455 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_968 : Covered ((1327 / 1600 : ℚ),(531 / 640 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (1327 / 1600 : ℚ) (531 / 640 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (455 / 12032 : ℚ) node_969 node_970
theorem node_967 : Covered ((1327 / 1600 : ℚ),(83 / 100 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (1327 / 1600 : ℚ) (83 / 100 : ℚ) (227 / 6016 : ℚ) (57 / 1504 : ℚ) (531 / 640 : ℚ) node_968 node_971
theorem node_966 : Covered ((1327 / 1600 : ℚ),(83 / 100 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_965 : Covered ((1327 / 1600 : ℚ),(83 / 100 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (1327 / 1600 : ℚ) (83 / 100 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_966 node_967
theorem node_964 : Covered ((663 / 800 : ℚ),(1327 / 1600 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_963 : Covered ((663 / 800 : ℚ),(1327 / 1600 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_962 : Covered ((663 / 800 : ℚ),(1327 / 1600 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (663 / 800 : ℚ) (1327 / 1600 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_963 node_964
theorem node_961 : Covered ((663 / 800 : ℚ),(83 / 100 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (663 / 800 : ℚ) (83 / 100 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (1327 / 1600 : ℚ) node_962 node_965
theorem node_960 : Covered ((663 / 800 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_959 : Covered ((663 / 800 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (663 / 800 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_960 node_961
theorem node_958 : Covered ((53 / 64 : ℚ),(663 / 800 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_957 : Covered ((53 / 64 : ℚ),(663 / 800 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_956 : Covered ((53 / 64 : ℚ),(663 / 800 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (53 / 64 : ℚ) (663 / 800 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_957 node_958
theorem node_955 : Covered ((331 / 400 : ℚ),(53 / 64 : ℚ)) ((227 / 6016 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_954 : Covered ((331 / 400 : ℚ),(53 / 64 : ℚ)) ((113 / 3008 : ℚ),(227 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_953 : Covered ((331 / 400 : ℚ),(53 / 64 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (53 / 64 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (227 / 6016 : ℚ) node_954 node_955
theorem node_952 : Covered ((331 / 400 : ℚ),(663 / 800 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (331 / 400 : ℚ) (663 / 800 : ℚ) (113 / 3008 : ℚ) (57 / 1504 : ℚ) (53 / 64 : ℚ) node_953 node_956
theorem node_951 : Covered ((331 / 400 : ℚ),(663 / 800 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_950 : Covered ((331 / 400 : ℚ),(663 / 800 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (663 / 800 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_951 node_952
theorem node_949 : Covered ((331 / 400 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (331 / 400 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (663 / 800 : ℚ) node_950 node_959
theorem node_948 : Covered ((331 / 400 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_949 node_974
theorem node_947 : Covered ((661 / 800 : ℚ),(331 / 400 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_946 : Covered ((2647 / 3200 : ℚ),(331 / 400 : ℚ)) ((459 / 12032 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_945 : Covered ((2647 / 3200 : ℚ),(331 / 400 : ℚ)) ((229 / 6016 : ℚ),(459 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_944 : Covered ((2647 / 3200 : ℚ),(331 / 400 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (2647 / 3200 : ℚ) (331 / 400 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (459 / 12032 : ℚ) node_945 node_946
theorem node_943 : Covered ((1323 / 1600 : ℚ),(2647 / 3200 : ℚ)) ((459 / 12032 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_942 : Covered ((1323 / 1600 : ℚ),(2647 / 3200 : ℚ)) ((229 / 6016 : ℚ),(459 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_941 : Covered ((1323 / 1600 : ℚ),(2647 / 3200 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (1323 / 1600 : ℚ) (2647 / 3200 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (459 / 12032 : ℚ) node_942 node_943
theorem node_940 : Covered ((1323 / 1600 : ℚ),(331 / 400 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (1323 / 1600 : ℚ) (331 / 400 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (2647 / 3200 : ℚ) node_941 node_944
theorem node_939 : Covered ((1323 / 1600 : ℚ),(331 / 400 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_938 : Covered ((1323 / 1600 : ℚ),(331 / 400 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (1323 / 1600 : ℚ) (331 / 400 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_939 node_940
theorem node_937 : Covered ((529 / 640 : ℚ),(1323 / 1600 : ℚ)) ((459 / 12032 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_936 : Covered ((529 / 640 : ℚ),(1323 / 1600 : ℚ)) ((229 / 6016 : ℚ),(459 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_935 : Covered ((529 / 640 : ℚ),(1323 / 1600 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (529 / 640 : ℚ) (1323 / 1600 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (459 / 12032 : ℚ) node_936 node_937
theorem node_934 : Covered ((661 / 800 : ℚ),(529 / 640 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_933 : Covered ((661 / 800 : ℚ),(1323 / 1600 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (661 / 800 : ℚ) (1323 / 1600 : ℚ) (229 / 6016 : ℚ) (115 / 3008 : ℚ) (529 / 640 : ℚ) node_934 node_935
theorem node_932 : Covered ((661 / 800 : ℚ),(1323 / 1600 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_931 : Covered ((661 / 800 : ℚ),(1323 / 1600 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (661 / 800 : ℚ) (1323 / 1600 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_932 node_933
theorem node_930 : Covered ((661 / 800 : ℚ),(331 / 400 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (661 / 800 : ℚ) (331 / 400 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (1323 / 1600 : ℚ) node_931 node_938
theorem node_929 : Covered ((661 / 800 : ℚ),(331 / 400 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (661 / 800 : ℚ) (331 / 400 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_930 node_947
theorem node_928 : Covered ((1321 / 1600 : ℚ),(661 / 800 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_927 : Covered ((2643 / 3200 : ℚ),(661 / 800 : ℚ)) ((461 / 12032 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_926 : Covered ((2643 / 3200 : ℚ),(661 / 800 : ℚ)) ((115 / 3008 : ℚ),(461 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_925 : Covered ((2643 / 3200 : ℚ),(661 / 800 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 exact split_j (2643 / 3200 : ℚ) (661 / 800 : ℚ) (115 / 3008 : ℚ) (231 / 6016 : ℚ) (461 / 12032 : ℚ) node_926 node_927
theorem node_924 : Covered ((1321 / 1600 : ℚ),(2643 / 3200 : ℚ)) ((461 / 12032 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_923 : Covered ((1321 / 1600 : ℚ),(2643 / 3200 : ℚ)) ((115 / 3008 : ℚ),(461 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_922 : Covered ((1321 / 1600 : ℚ),(2643 / 3200 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 exact split_j (1321 / 1600 : ℚ) (2643 / 3200 : ℚ) (115 / 3008 : ℚ) (231 / 6016 : ℚ) (461 / 12032 : ℚ) node_923 node_924
theorem node_921 : Covered ((1321 / 1600 : ℚ),(661 / 800 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 exact split_c (1321 / 1600 : ℚ) (661 / 800 : ℚ) (115 / 3008 : ℚ) (231 / 6016 : ℚ) (2643 / 3200 : ℚ) node_922 node_925
theorem node_920 : Covered ((1321 / 1600 : ℚ),(661 / 800 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (1321 / 1600 : ℚ) (661 / 800 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_921 node_928
theorem node_919 : Covered ((33 / 40 : ℚ),(1321 / 1600 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_918 : Covered ((2641 / 3200 : ℚ),(1321 / 1600 : ℚ)) ((461 / 12032 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_917 : Covered ((2641 / 3200 : ℚ),(1321 / 1600 : ℚ)) ((115 / 3008 : ℚ),(461 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_916 : Covered ((2641 / 3200 : ℚ),(1321 / 1600 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 exact split_j (2641 / 3200 : ℚ) (1321 / 1600 : ℚ) (115 / 3008 : ℚ) (231 / 6016 : ℚ) (461 / 12032 : ℚ) node_917 node_918
theorem node_915 : Covered ((33 / 40 : ℚ),(2641 / 3200 : ℚ)) ((461 / 12032 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_914 : Covered ((33 / 40 : ℚ),(2641 / 3200 : ℚ)) ((115 / 3008 : ℚ),(461 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_913 : Covered ((33 / 40 : ℚ),(2641 / 3200 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (2641 / 3200 : ℚ) (115 / 3008 : ℚ) (231 / 6016 : ℚ) (461 / 12032 : ℚ) node_914 node_915
theorem node_912 : Covered ((33 / 40 : ℚ),(1321 / 1600 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (1321 / 1600 : ℚ) (115 / 3008 : ℚ) (231 / 6016 : ℚ) (2641 / 3200 : ℚ) node_913 node_916
theorem node_911 : Covered ((33 / 40 : ℚ),(1321 / 1600 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (1321 / 1600 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_912 node_919
theorem node_910 : Covered ((33 / 40 : ℚ),(661 / 800 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (661 / 800 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (1321 / 1600 : ℚ) node_911 node_920
theorem node_909 : Covered ((1321 / 1600 : ℚ),(661 / 800 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_908 : Covered ((1321 / 1600 : ℚ),(661 / 800 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_907 : Covered ((1321 / 1600 : ℚ),(661 / 800 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (1321 / 1600 : ℚ) (661 / 800 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_908 node_909
theorem node_906 : Covered ((33 / 40 : ℚ),(1321 / 1600 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_905 : Covered ((33 / 40 : ℚ),(1321 / 1600 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_904 : Covered ((33 / 40 : ℚ),(1321 / 1600 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (1321 / 1600 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_905 node_906
theorem node_903 : Covered ((33 / 40 : ℚ),(661 / 800 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (661 / 800 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (1321 / 1600 : ℚ) node_904 node_907
theorem node_902 : Covered ((33 / 40 : ℚ),(661 / 800 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (661 / 800 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_903 node_910
theorem node_901 : Covered ((33 / 40 : ℚ),(331 / 400 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (331 / 400 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (661 / 800 : ℚ) node_902 node_929
theorem node_900 : Covered ((661 / 800 : ℚ),(331 / 400 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_899 : Covered ((661 / 800 : ℚ),(331 / 400 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_898 : Covered ((661 / 800 : ℚ),(331 / 400 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (661 / 800 : ℚ) (331 / 400 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_899 node_900
theorem node_897 : Covered ((33 / 40 : ℚ),(661 / 800 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_896 : Covered ((33 / 40 : ℚ),(661 / 800 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_895 : Covered ((33 / 40 : ℚ),(661 / 800 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (661 / 800 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_896 node_897
theorem node_894 : Covered ((33 / 40 : ℚ),(331 / 400 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (331 / 400 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (661 / 800 : ℚ) node_895 node_898
theorem node_893 : Covered ((33 / 40 : ℚ),(331 / 400 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (331 / 400 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_894 node_901
theorem node_892 : Covered ((33 / 40 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (331 / 400 : ℚ) node_893 node_948
theorem node_891 : Covered ((33 / 40 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_892 node_1011
theorem node_890 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_889 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_888 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_887 : Covered ((1317 / 1600 : ℚ),(659 / 800 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_886 : Covered ((329 / 400 : ℚ),(1317 / 1600 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_885 : Covered ((2633 / 3200 : ℚ),(1317 / 1600 : ℚ)) ((465 / 12032 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_884 : Covered ((2633 / 3200 : ℚ),(1317 / 1600 : ℚ)) ((29 / 752 : ℚ),(465 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_883 : Covered ((2633 / 3200 : ℚ),(1317 / 1600 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 exact split_j (2633 / 3200 : ℚ) (1317 / 1600 : ℚ) (29 / 752 : ℚ) (233 / 6016 : ℚ) (465 / 12032 : ℚ) node_884 node_885
theorem node_882 : Covered ((329 / 400 : ℚ),(2633 / 3200 : ℚ)) ((465 / 12032 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_881 : Covered ((329 / 400 : ℚ),(2633 / 3200 : ℚ)) ((29 / 752 : ℚ),(465 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_880 : Covered ((329 / 400 : ℚ),(2633 / 3200 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (2633 / 3200 : ℚ) (29 / 752 : ℚ) (233 / 6016 : ℚ) (465 / 12032 : ℚ) node_881 node_882
theorem node_879 : Covered ((329 / 400 : ℚ),(1317 / 1600 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 exact split_c (329 / 400 : ℚ) (1317 / 1600 : ℚ) (29 / 752 : ℚ) (233 / 6016 : ℚ) (2633 / 3200 : ℚ) node_880 node_883
theorem node_878 : Covered ((329 / 400 : ℚ),(1317 / 1600 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (1317 / 1600 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_879 node_886
theorem node_877 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_c (329 / 400 : ℚ) (659 / 800 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (1317 / 1600 : ℚ) node_878 node_887
theorem node_876 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (659 / 800 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_877 node_888
theorem node_875 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (329 / 400 : ℚ) (33 / 40 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (659 / 800 : ℚ) node_876 node_889
theorem node_874 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (33 / 40 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_875 node_890
theorem node_873 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_872 : Covered ((657 / 800 : ℚ),(329 / 400 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_871 : Covered ((263 / 320 : ℚ),(329 / 400 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_870 : Covered ((2631 / 3200 : ℚ),(329 / 400 : ℚ)) ((465 / 12032 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_869 : Covered ((2631 / 3200 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(465 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_868 : Covered ((2631 / 3200 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 exact split_j (2631 / 3200 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (233 / 6016 : ℚ) (465 / 12032 : ℚ) node_869 node_870
theorem node_867 : Covered ((263 / 320 : ℚ),(2631 / 3200 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_866 : Covered ((263 / 320 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 exact split_c (263 / 320 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (233 / 6016 : ℚ) (2631 / 3200 : ℚ) node_867 node_868
theorem node_865 : Covered ((263 / 320 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (263 / 320 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_866 node_871
theorem node_864 : Covered ((2629 / 3200 : ℚ),(263 / 320 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_863 : Covered ((657 / 800 : ℚ),(2629 / 3200 : ℚ)) ((467 / 12032 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_862 : Covered ((657 / 800 : ℚ),(2629 / 3200 : ℚ)) ((233 / 6016 : ℚ),(467 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_861 : Covered ((657 / 800 : ℚ),(2629 / 3200 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (657 / 800 : ℚ) (2629 / 3200 : ℚ) (233 / 6016 : ℚ) (117 / 3008 : ℚ) (467 / 12032 : ℚ) node_862 node_863
theorem node_860 : Covered ((657 / 800 : ℚ),(263 / 320 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_c (657 / 800 : ℚ) (263 / 320 : ℚ) (233 / 6016 : ℚ) (117 / 3008 : ℚ) (2629 / 3200 : ℚ) node_861 node_864
theorem node_859 : Covered ((657 / 800 : ℚ),(263 / 320 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_858 : Covered ((657 / 800 : ℚ),(263 / 320 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (657 / 800 : ℚ) (263 / 320 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_859 node_860
theorem node_857 : Covered ((657 / 800 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_c (657 / 800 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (263 / 320 : ℚ) node_858 node_865
theorem node_856 : Covered ((657 / 800 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (657 / 800 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_857 node_872
theorem node_855 : Covered ((41 / 50 : ℚ),(657 / 800 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_854 : Covered ((2627 / 3200 : ℚ),(657 / 800 : ℚ)) ((467 / 12032 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_853 : Covered ((2627 / 3200 : ℚ),(657 / 800 : ℚ)) ((233 / 6016 : ℚ),(467 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_852 : Covered ((2627 / 3200 : ℚ),(657 / 800 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (2627 / 3200 : ℚ) (657 / 800 : ℚ) (233 / 6016 : ℚ) (117 / 3008 : ℚ) (467 / 12032 : ℚ) node_853 node_854
theorem node_851 : Covered ((1313 / 1600 : ℚ),(2627 / 3200 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_850 : Covered ((1313 / 1600 : ℚ),(657 / 800 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_c (1313 / 1600 : ℚ) (657 / 800 : ℚ) (233 / 6016 : ℚ) (117 / 3008 : ℚ) (2627 / 3200 : ℚ) node_851 node_852
theorem node_849 : Covered ((1313 / 1600 : ℚ),(657 / 800 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_848 : Covered ((1313 / 1600 : ℚ),(657 / 800 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (1313 / 1600 : ℚ) (657 / 800 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_849 node_850
theorem node_847 : Covered ((41 / 50 : ℚ),(1313 / 1600 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_846 : Covered ((41 / 50 : ℚ),(1313 / 1600 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_845 : Covered ((41 / 50 : ℚ),(1313 / 1600 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (1313 / 1600 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_846 node_847
theorem node_844 : Covered ((41 / 50 : ℚ),(657 / 800 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (657 / 800 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (1313 / 1600 : ℚ) node_845 node_848
theorem node_843 : Covered ((41 / 50 : ℚ),(657 / 800 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (657 / 800 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_844 node_855
theorem node_842 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (657 / 800 : ℚ) node_843 node_856
theorem node_841 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (329 / 400 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_842 node_873
theorem node_840 : Covered ((41 / 50 : ℚ),(33 / 40 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (33 / 40 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (329 / 400 : ℚ) node_841 node_874
theorem node_839 : Covered ((2639 / 3200 : ℚ),(33 / 40 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_838 : Covered ((1319 / 1600 : ℚ),(2639 / 3200 : ℚ)) ((463 / 12032 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_837 : Covered ((1319 / 1600 : ℚ),(2639 / 3200 : ℚ)) ((231 / 6016 : ℚ),(463 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_836 : Covered ((1319 / 1600 : ℚ),(2639 / 3200 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (1319 / 1600 : ℚ) (2639 / 3200 : ℚ) (231 / 6016 : ℚ) (29 / 752 : ℚ) (463 / 12032 : ℚ) node_837 node_838
theorem node_835 : Covered ((1319 / 1600 : ℚ),(33 / 40 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (1319 / 1600 : ℚ) (33 / 40 : ℚ) (231 / 6016 : ℚ) (29 / 752 : ℚ) (2639 / 3200 : ℚ) node_836 node_839
theorem node_834 : Covered ((1319 / 1600 : ℚ),(33 / 40 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_833 : Covered ((1319 / 1600 : ℚ),(33 / 40 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (1319 / 1600 : ℚ) (33 / 40 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_834 node_835
theorem node_832 : Covered ((2637 / 3200 : ℚ),(1319 / 1600 : ℚ)) ((463 / 12032 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_831 : Covered ((2637 / 3200 : ℚ),(1319 / 1600 : ℚ)) ((231 / 6016 : ℚ),(463 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_830 : Covered ((2637 / 3200 : ℚ),(1319 / 1600 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (2637 / 3200 : ℚ) (1319 / 1600 : ℚ) (231 / 6016 : ℚ) (29 / 752 : ℚ) (463 / 12032 : ℚ) node_831 node_832
theorem node_829 : Covered ((659 / 800 : ℚ),(2637 / 3200 : ℚ)) ((463 / 12032 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_828 : Covered ((659 / 800 : ℚ),(2637 / 3200 : ℚ)) ((231 / 6016 : ℚ),(463 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_827 : Covered ((659 / 800 : ℚ),(2637 / 3200 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (659 / 800 : ℚ) (2637 / 3200 : ℚ) (231 / 6016 : ℚ) (29 / 752 : ℚ) (463 / 12032 : ℚ) node_828 node_829
theorem node_826 : Covered ((659 / 800 : ℚ),(1319 / 1600 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (659 / 800 : ℚ) (1319 / 1600 : ℚ) (231 / 6016 : ℚ) (29 / 752 : ℚ) (2637 / 3200 : ℚ) node_827 node_830
theorem node_825 : Covered ((659 / 800 : ℚ),(1319 / 1600 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_824 : Covered ((659 / 800 : ℚ),(1319 / 1600 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (659 / 800 : ℚ) (1319 / 1600 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_825 node_826
theorem node_823 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (659 / 800 : ℚ) (33 / 40 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (1319 / 1600 : ℚ) node_824 node_833
theorem node_822 : Covered ((1319 / 1600 : ℚ),(33 / 40 : ℚ)) ((229 / 6016 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_821 : Covered ((1319 / 1600 : ℚ),(33 / 40 : ℚ)) ((57 / 1504 : ℚ),(229 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_820 : Covered ((1319 / 1600 : ℚ),(33 / 40 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_j (1319 / 1600 : ℚ) (33 / 40 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (229 / 6016 : ℚ) node_821 node_822
theorem node_819 : Covered ((659 / 800 : ℚ),(1319 / 1600 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_818 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 exact split_c (659 / 800 : ℚ) (33 / 40 : ℚ) (57 / 1504 : ℚ) (115 / 3008 : ℚ) (1319 / 1600 : ℚ) node_819 node_820
theorem node_817 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (659 / 800 : ℚ) (33 / 40 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_818 node_823
theorem node_816 : Covered ((527 / 640 : ℚ),(659 / 800 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_815 : Covered ((1317 / 1600 : ℚ),(527 / 640 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_814 : Covered ((1317 / 1600 : ℚ),(659 / 800 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (1317 / 1600 : ℚ) (659 / 800 : ℚ) (231 / 6016 : ℚ) (29 / 752 : ℚ) (527 / 640 : ℚ) node_815 node_816
theorem node_813 : Covered ((1317 / 1600 : ℚ),(659 / 800 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_812 : Covered ((1317 / 1600 : ℚ),(659 / 800 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (1317 / 1600 : ℚ) (659 / 800 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_813 node_814
theorem node_811 : Covered ((329 / 400 : ℚ),(1317 / 1600 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_810 : Covered ((329 / 400 : ℚ),(1317 / 1600 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_809 : Covered ((329 / 400 : ℚ),(1317 / 1600 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (1317 / 1600 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_810 node_811
theorem node_808 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (329 / 400 : ℚ) (659 / 800 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (1317 / 1600 : ℚ) node_809 node_812
theorem node_807 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_806 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (659 / 800 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_807 node_808
theorem node_805 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (329 / 400 : ℚ) (33 / 40 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (659 / 800 : ℚ) node_806 node_817
theorem node_804 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((113 / 3008 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_803 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((7 / 188 : ℚ),(113 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_802 : Covered ((659 / 800 : ℚ),(33 / 40 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_j (659 / 800 : ℚ) (33 / 40 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (113 / 3008 : ℚ) node_803 node_804
theorem node_801 : Covered ((329 / 400 : ℚ),(659 / 800 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_800 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 exact split_c (329 / 400 : ℚ) (33 / 40 : ℚ) (7 / 188 : ℚ) (57 / 1504 : ℚ) (659 / 800 : ℚ) node_801 node_802
theorem node_799 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (33 / 40 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_800 node_805
theorem node_798 : Covered ((263 / 320 : ℚ),(329 / 400 : ℚ)) ((231 / 6016 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_797 : Covered ((263 / 320 : ℚ),(329 / 400 : ℚ)) ((115 / 3008 : ℚ),(231 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_796 : Covered ((263 / 320 : ℚ),(329 / 400 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (263 / 320 : ℚ) (329 / 400 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (231 / 6016 : ℚ) node_797 node_798
theorem node_795 : Covered ((657 / 800 : ℚ),(263 / 320 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_794 : Covered ((657 / 800 : ℚ),(329 / 400 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (657 / 800 : ℚ) (329 / 400 : ℚ) (115 / 3008 : ℚ) (29 / 752 : ℚ) (263 / 320 : ℚ) node_795 node_796
theorem node_793 : Covered ((657 / 800 : ℚ),(329 / 400 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_792 : Covered ((657 / 800 : ℚ),(329 / 400 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (657 / 800 : ℚ) (329 / 400 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_793 node_794
theorem node_791 : Covered ((41 / 50 : ℚ),(657 / 800 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_790 : Covered ((41 / 50 : ℚ),(657 / 800 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_789 : Covered ((41 / 50 : ℚ),(657 / 800 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (657 / 800 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_790 node_791
theorem node_788 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (329 / 400 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (657 / 800 : ℚ) node_789 node_792
theorem node_787 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_786 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (329 / 400 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_787 node_788
theorem node_785 : Covered ((41 / 50 : ℚ),(33 / 40 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (33 / 40 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (329 / 400 : ℚ) node_786 node_799
theorem node_784 : Covered ((41 / 50 : ℚ),(33 / 40 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (33 / 40 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_785 node_840
theorem node_783 : Covered ((41 / 50 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (33 / 40 : ℚ) node_784 node_891
theorem node_782 : Covered ((41 / 50 : ℚ),(83 / 100 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (83 / 100 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_783 node_1012
theorem node_781 : Covered ((41 / 50 : ℚ),(21 / 25 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (21 / 25 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (83 / 100 : ℚ) node_782 node_1013
theorem node_780 : Covered ((671 / 800 : ℚ),(21 / 25 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_779 : Covered ((2687 / 3200 : ℚ),(21 / 25 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_778 : Covered ((2687 / 3200 : ℚ),(21 / 25 : ℚ)) ((221 / 6016 : ℚ),(443 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_777 : Covered ((2687 / 3200 : ℚ),(21 / 25 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (2687 / 3200 : ℚ) (21 / 25 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (443 / 12032 : ℚ) node_778 node_779
theorem node_776 : Covered ((1343 / 1600 : ℚ),(2687 / 3200 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_775 : Covered ((1343 / 1600 : ℚ),(2687 / 3200 : ℚ)) ((221 / 6016 : ℚ),(443 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_774 : Covered ((1343 / 1600 : ℚ),(2687 / 3200 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (1343 / 1600 : ℚ) (2687 / 3200 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (443 / 12032 : ℚ) node_775 node_776
theorem node_773 : Covered ((1343 / 1600 : ℚ),(21 / 25 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (1343 / 1600 : ℚ) (21 / 25 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (2687 / 3200 : ℚ) node_774 node_777
theorem node_772 : Covered ((2687 / 3200 : ℚ),(21 / 25 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_771 : Covered ((1343 / 1600 : ℚ),(2687 / 3200 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_770 : Covered ((1343 / 1600 : ℚ),(21 / 25 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 exact split_c (1343 / 1600 : ℚ) (21 / 25 : ℚ) (55 / 1504 : ℚ) (221 / 6016 : ℚ) (2687 / 3200 : ℚ) node_771 node_772
theorem node_769 : Covered ((1343 / 1600 : ℚ),(21 / 25 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (1343 / 1600 : ℚ) (21 / 25 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_770 node_773
theorem node_768 : Covered ((5371 / 6400 : ℚ),(1343 / 1600 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_767 : Covered ((537 / 640 : ℚ),(5371 / 6400 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_766 : Covered ((537 / 640 : ℚ),(1343 / 1600 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (537 / 640 : ℚ) (1343 / 1600 : ℚ) (443 / 12032 : ℚ) (111 / 3008 : ℚ) (5371 / 6400 : ℚ) node_767 node_768
theorem node_765 : Covered ((537 / 640 : ℚ),(1343 / 1600 : ℚ)) ((221 / 6016 : ℚ),(443 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_764 : Covered ((537 / 640 : ℚ),(1343 / 1600 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (537 / 640 : ℚ) (1343 / 1600 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (443 / 12032 : ℚ) node_765 node_766
theorem node_763 : Covered ((671 / 800 : ℚ),(537 / 640 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_762 : Covered ((671 / 800 : ℚ),(537 / 640 : ℚ)) ((221 / 6016 : ℚ),(443 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_761 : Covered ((671 / 800 : ℚ),(537 / 640 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (671 / 800 : ℚ) (537 / 640 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (443 / 12032 : ℚ) node_762 node_763
theorem node_760 : Covered ((671 / 800 : ℚ),(1343 / 1600 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (671 / 800 : ℚ) (1343 / 1600 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (537 / 640 : ℚ) node_761 node_764
theorem node_759 : Covered ((671 / 800 : ℚ),(1343 / 1600 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_758 : Covered ((671 / 800 : ℚ),(1343 / 1600 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (671 / 800 : ℚ) (1343 / 1600 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_759 node_760
theorem node_757 : Covered ((671 / 800 : ℚ),(21 / 25 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (671 / 800 : ℚ) (21 / 25 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (1343 / 1600 : ℚ) node_758 node_769
theorem node_756 : Covered ((671 / 800 : ℚ),(21 / 25 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (671 / 800 : ℚ) (21 / 25 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_757 node_780
theorem node_755 : Covered ((1341 / 1600 : ℚ),(671 / 800 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_754 : Covered ((2683 / 3200 : ℚ),(671 / 800 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_753 : Covered ((1341 / 1600 : ℚ),(2683 / 3200 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_752 : Covered ((1341 / 1600 : ℚ),(2683 / 3200 : ℚ)) ((111 / 3008 : ℚ),(445 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_751 : Covered ((1341 / 1600 : ℚ),(2683 / 3200 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_j (1341 / 1600 : ℚ) (2683 / 3200 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (445 / 12032 : ℚ) node_752 node_753
theorem node_750 : Covered ((1341 / 1600 : ℚ),(671 / 800 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_c (1341 / 1600 : ℚ) (671 / 800 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (2683 / 3200 : ℚ) node_751 node_754
theorem node_749 : Covered ((1341 / 1600 : ℚ),(671 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (1341 / 1600 : ℚ) (671 / 800 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_750 node_755
theorem node_748 : Covered ((67 / 80 : ℚ),(1341 / 1600 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_747 : Covered ((2681 / 3200 : ℚ),(1341 / 1600 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_746 : Covered ((2681 / 3200 : ℚ),(1341 / 1600 : ℚ)) ((111 / 3008 : ℚ),(445 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_745 : Covered ((2681 / 3200 : ℚ),(1341 / 1600 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_j (2681 / 3200 : ℚ) (1341 / 1600 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (445 / 12032 : ℚ) node_746 node_747
theorem node_744 : Covered ((5361 / 6400 : ℚ),(2681 / 3200 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_743 : Covered ((67 / 80 : ℚ),(5361 / 6400 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_742 : Covered ((67 / 80 : ℚ),(2681 / 3200 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_c (67 / 80 : ℚ) (2681 / 3200 : ℚ) (445 / 12032 : ℚ) (223 / 6016 : ℚ) (5361 / 6400 : ℚ) node_743 node_744
theorem node_741 : Covered ((67 / 80 : ℚ),(2681 / 3200 : ℚ)) ((111 / 3008 : ℚ),(445 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_740 : Covered ((67 / 80 : ℚ),(2681 / 3200 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (2681 / 3200 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (445 / 12032 : ℚ) node_741 node_742
theorem node_739 : Covered ((67 / 80 : ℚ),(1341 / 1600 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_c (67 / 80 : ℚ) (1341 / 1600 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (2681 / 3200 : ℚ) node_740 node_745
theorem node_738 : Covered ((67 / 80 : ℚ),(1341 / 1600 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (1341 / 1600 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_739 node_748
theorem node_737 : Covered ((67 / 80 : ℚ),(671 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (67 / 80 : ℚ) (671 / 800 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (1341 / 1600 : ℚ) node_738 node_749
theorem node_736 : Covered ((2683 / 3200 : ℚ),(671 / 800 : ℚ)) ((443 / 12032 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_735 : Covered ((2683 / 3200 : ℚ),(671 / 800 : ℚ)) ((221 / 6016 : ℚ),(443 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_734 : Covered ((2683 / 3200 : ℚ),(671 / 800 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (2683 / 3200 : ℚ) (671 / 800 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (443 / 12032 : ℚ) node_735 node_736
theorem node_733 : Covered ((1341 / 1600 : ℚ),(2683 / 3200 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_732 : Covered ((1341 / 1600 : ℚ),(671 / 800 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (1341 / 1600 : ℚ) (671 / 800 : ℚ) (221 / 6016 : ℚ) (111 / 3008 : ℚ) (2683 / 3200 : ℚ) node_733 node_734
theorem node_731 : Covered ((1341 / 1600 : ℚ),(671 / 800 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_730 : Covered ((1341 / 1600 : ℚ),(671 / 800 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (1341 / 1600 : ℚ) (671 / 800 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_731 node_732
theorem node_729 : Covered ((67 / 80 : ℚ),(1341 / 1600 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_728 : Covered ((67 / 80 : ℚ),(1341 / 1600 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_727 : Covered ((67 / 80 : ℚ),(1341 / 1600 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (1341 / 1600 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_728 node_729
theorem node_726 : Covered ((67 / 80 : ℚ),(671 / 800 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (67 / 80 : ℚ) (671 / 800 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (1341 / 1600 : ℚ) node_727 node_730
theorem node_725 : Covered ((67 / 80 : ℚ),(671 / 800 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (671 / 800 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_726 node_737
theorem node_724 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (67 / 80 : ℚ) (21 / 25 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (671 / 800 : ℚ) node_725 node_756
theorem node_723 : Covered ((1343 / 1600 : ℚ),(21 / 25 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_722 : Covered ((671 / 800 : ℚ),(1343 / 1600 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_721 : Covered ((671 / 800 : ℚ),(21 / 25 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (671 / 800 : ℚ) (21 / 25 : ℚ) (109 / 3008 : ℚ) (55 / 1504 : ℚ) (1343 / 1600 : ℚ) node_722 node_723
theorem node_720 : Covered ((671 / 800 : ℚ),(21 / 25 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_719 : Covered ((671 / 800 : ℚ),(21 / 25 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (671 / 800 : ℚ) (21 / 25 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_720 node_721
theorem node_718 : Covered ((67 / 80 : ℚ),(671 / 800 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_717 : Covered ((67 / 80 : ℚ),(671 / 800 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_716 : Covered ((67 / 80 : ℚ),(671 / 800 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (671 / 800 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_717 node_718
theorem node_715 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (67 / 80 : ℚ) (21 / 25 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (671 / 800 : ℚ) node_716 node_719
theorem node_714 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (21 / 25 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_715 node_724
theorem node_713 : Covered ((2679 / 3200 : ℚ),(67 / 80 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_712 : Covered ((1339 / 1600 : ℚ),(2679 / 3200 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_711 : Covered ((5357 / 6400 : ℚ),(2679 / 3200 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_710 : Covered ((1339 / 1600 : ℚ),(5357 / 6400 : ℚ)) ((19 / 512 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_709 : Covered ((1339 / 1600 : ℚ),(5357 / 6400 : ℚ)) ((223 / 6016 : ℚ),(19 / 512 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_708 : Covered ((1339 / 1600 : ℚ),(5357 / 6400 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 exact split_j (1339 / 1600 : ℚ) (5357 / 6400 : ℚ) (223 / 6016 : ℚ) (447 / 12032 : ℚ) (19 / 512 : ℚ) node_709 node_710
theorem node_707 : Covered ((1339 / 1600 : ℚ),(2679 / 3200 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 exact split_c (1339 / 1600 : ℚ) (2679 / 3200 : ℚ) (223 / 6016 : ℚ) (447 / 12032 : ℚ) (5357 / 6400 : ℚ) node_708 node_711
theorem node_706 : Covered ((1339 / 1600 : ℚ),(2679 / 3200 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (1339 / 1600 : ℚ) (2679 / 3200 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (447 / 12032 : ℚ) node_707 node_712
theorem node_705 : Covered ((1339 / 1600 : ℚ),(67 / 80 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (1339 / 1600 : ℚ) (67 / 80 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (2679 / 3200 : ℚ) node_706 node_713
theorem node_704 : Covered ((2679 / 3200 : ℚ),(67 / 80 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_703 : Covered ((2679 / 3200 : ℚ),(67 / 80 : ℚ)) ((111 / 3008 : ℚ),(445 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_702 : Covered ((2679 / 3200 : ℚ),(67 / 80 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_j (2679 / 3200 : ℚ) (67 / 80 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (445 / 12032 : ℚ) node_703 node_704
theorem node_701 : Covered ((1339 / 1600 : ℚ),(2679 / 3200 : ℚ)) ((445 / 12032 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_700 : Covered ((1339 / 1600 : ℚ),(2679 / 3200 : ℚ)) ((111 / 3008 : ℚ),(445 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_699 : Covered ((1339 / 1600 : ℚ),(2679 / 3200 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_j (1339 / 1600 : ℚ) (2679 / 3200 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (445 / 12032 : ℚ) node_700 node_701
theorem node_698 : Covered ((1339 / 1600 : ℚ),(67 / 80 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_c (1339 / 1600 : ℚ) (67 / 80 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (2679 / 3200 : ℚ) node_699 node_702
theorem node_697 : Covered ((1339 / 1600 : ℚ),(67 / 80 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (1339 / 1600 : ℚ) (67 / 80 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_698 node_705
theorem node_696 : Covered ((2677 / 3200 : ℚ),(1339 / 1600 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_695 : Covered ((2677 / 3200 : ℚ),(1339 / 1600 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_694 : Covered ((2677 / 3200 : ℚ),(1339 / 1600 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (2677 / 3200 : ℚ) (1339 / 1600 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (447 / 12032 : ℚ) node_695 node_696
theorem node_693 : Covered ((669 / 800 : ℚ),(2677 / 3200 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_692 : Covered ((669 / 800 : ℚ),(2677 / 3200 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_691 : Covered ((669 / 800 : ℚ),(2677 / 3200 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (669 / 800 : ℚ) (2677 / 3200 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (447 / 12032 : ℚ) node_692 node_693
theorem node_690 : Covered ((669 / 800 : ℚ),(1339 / 1600 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (669 / 800 : ℚ) (1339 / 1600 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (2677 / 3200 : ℚ) node_691 node_694
theorem node_689 : Covered ((2677 / 3200 : ℚ),(1339 / 1600 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_688 : Covered ((669 / 800 : ℚ),(2677 / 3200 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_687 : Covered ((669 / 800 : ℚ),(1339 / 1600 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 exact split_c (669 / 800 : ℚ) (1339 / 1600 : ℚ) (111 / 3008 : ℚ) (223 / 6016 : ℚ) (2677 / 3200 : ℚ) node_688 node_689
theorem node_686 : Covered ((669 / 800 : ℚ),(1339 / 1600 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (669 / 800 : ℚ) (1339 / 1600 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_687 node_690
theorem node_685 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (669 / 800 : ℚ) (67 / 80 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (1339 / 1600 : ℚ) node_686 node_697
theorem node_684 : Covered ((1339 / 1600 : ℚ),(67 / 80 : ℚ)) ((221 / 6016 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_683 : Covered ((1339 / 1600 : ℚ),(67 / 80 : ℚ)) ((55 / 1504 : ℚ),(221 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_682 : Covered ((1339 / 1600 : ℚ),(67 / 80 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_j (1339 / 1600 : ℚ) (67 / 80 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (221 / 6016 : ℚ) node_683 node_684
theorem node_681 : Covered ((669 / 800 : ℚ),(1339 / 1600 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_680 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 exact split_c (669 / 800 : ℚ) (67 / 80 : ℚ) (55 / 1504 : ℚ) (111 / 3008 : ℚ) (1339 / 1600 : ℚ) node_681 node_682
theorem node_679 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (669 / 800 : ℚ) (67 / 80 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_680 node_685
theorem node_678 : Covered ((5351 / 6400 : ℚ),(669 / 800 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_677 : Covered ((107 / 128 : ℚ),(5351 / 6400 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_676 : Covered ((107 / 128 : ℚ),(669 / 800 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (107 / 128 : ℚ) (669 / 800 : ℚ) (447 / 12032 : ℚ) (7 / 188 : ℚ) (5351 / 6400 : ℚ) node_677 node_678
theorem node_675 : Covered ((107 / 128 : ℚ),(669 / 800 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_674 : Covered ((107 / 128 : ℚ),(669 / 800 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (107 / 128 : ℚ) (669 / 800 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (447 / 12032 : ℚ) node_675 node_676
theorem node_673 : Covered ((1337 / 1600 : ℚ),(107 / 128 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_672 : Covered ((1337 / 1600 : ℚ),(107 / 128 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_671 : Covered ((1337 / 1600 : ℚ),(107 / 128 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (1337 / 1600 : ℚ) (107 / 128 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (447 / 12032 : ℚ) node_672 node_673
theorem node_670 : Covered ((1337 / 1600 : ℚ),(669 / 800 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (1337 / 1600 : ℚ) (669 / 800 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (107 / 128 : ℚ) node_671 node_674
theorem node_669 : Covered ((1337 / 1600 : ℚ),(669 / 800 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_668 : Covered ((1337 / 1600 : ℚ),(669 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (1337 / 1600 : ℚ) (669 / 800 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_669 node_670
theorem node_667 : Covered ((2673 / 3200 : ℚ),(1337 / 1600 : ℚ)) ((447 / 12032 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_666 : Covered ((2673 / 3200 : ℚ),(1337 / 1600 : ℚ)) ((223 / 6016 : ℚ),(447 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_665 : Covered ((2673 / 3200 : ℚ),(1337 / 1600 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (2673 / 3200 : ℚ) (1337 / 1600 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (447 / 12032 : ℚ) node_666 node_667
theorem node_664 : Covered ((167 / 200 : ℚ),(2673 / 3200 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_663 : Covered ((167 / 200 : ℚ),(1337 / 1600 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (1337 / 1600 : ℚ) (223 / 6016 : ℚ) (7 / 188 : ℚ) (2673 / 3200 : ℚ) node_664 node_665
theorem node_662 : Covered ((167 / 200 : ℚ),(1337 / 1600 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_661 : Covered ((167 / 200 : ℚ),(1337 / 1600 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (1337 / 1600 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_662 node_663
theorem node_660 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (669 / 800 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (1337 / 1600 : ℚ) node_661 node_668
theorem node_659 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_658 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (669 / 800 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_659 node_660
theorem node_657 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (67 / 80 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (669 / 800 : ℚ) node_658 node_679
theorem node_656 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((109 / 3008 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_655 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((27 / 752 : ℚ),(109 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_654 : Covered ((669 / 800 : ℚ),(67 / 80 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_j (669 / 800 : ℚ) (67 / 80 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (109 / 3008 : ℚ) node_655 node_656
theorem node_653 : Covered ((167 / 200 : ℚ),(669 / 800 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_652 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (67 / 80 : ℚ) (27 / 752 : ℚ) (55 / 1504 : ℚ) (669 / 800 : ℚ) node_653 node_654
theorem node_651 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (67 / 80 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_652 node_657
theorem node_650 : Covered ((167 / 200 : ℚ),(21 / 25 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (21 / 25 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (67 / 80 : ℚ) node_651 node_714
theorem node_649 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_648 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_647 : Covered ((67 / 80 : ℚ),(21 / 25 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (67 / 80 : ℚ) (21 / 25 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_648 node_649
theorem node_646 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((53 / 1504 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_645 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((13 / 376 : ℚ),(53 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_644 : Covered ((167 / 200 : ℚ),(67 / 80 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (67 / 80 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (53 / 1504 : ℚ) node_645 node_646
theorem node_643 : Covered ((167 / 200 : ℚ),(21 / 25 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 exact split_c (167 / 200 : ℚ) (21 / 25 : ℚ) (13 / 376 : ℚ) (27 / 752 : ℚ) (67 / 80 : ℚ) node_644 node_647
theorem node_642 : Covered ((167 / 200 : ℚ),(21 / 25 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (167 / 200 : ℚ) (21 / 25 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_643 node_650
theorem node_641 : Covered ((267 / 320 : ℚ),(167 / 200 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_640 : Covered ((267 / 320 : ℚ),(167 / 200 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_639 : Covered ((267 / 320 : ℚ),(167 / 200 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (267 / 320 : ℚ) (167 / 200 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_640 node_641
theorem node_638 : Covered ((667 / 800 : ℚ),(267 / 320 : ℚ)) ((223 / 6016 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_637 : Covered ((667 / 800 : ℚ),(267 / 320 : ℚ)) ((111 / 3008 : ℚ),(223 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_636 : Covered ((667 / 800 : ℚ),(267 / 320 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (667 / 800 : ℚ) (267 / 320 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (223 / 6016 : ℚ) node_637 node_638
theorem node_635 : Covered ((667 / 800 : ℚ),(167 / 200 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (667 / 800 : ℚ) (167 / 200 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (267 / 320 : ℚ) node_636 node_639
theorem node_634 : Covered ((667 / 800 : ℚ),(167 / 200 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_633 : Covered ((667 / 800 : ℚ),(167 / 200 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (667 / 800 : ℚ) (167 / 200 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_634 node_635
theorem node_632 : Covered ((1333 / 1600 : ℚ),(667 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_631 : Covered ((333 / 400 : ℚ),(1333 / 1600 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_630 : Covered ((333 / 400 : ℚ),(667 / 800 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (333 / 400 : ℚ) (667 / 800 : ℚ) (111 / 3008 : ℚ) (7 / 188 : ℚ) (1333 / 1600 : ℚ) node_631 node_632
theorem node_629 : Covered ((333 / 400 : ℚ),(667 / 800 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_628 : Covered ((333 / 400 : ℚ),(667 / 800 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (333 / 400 : ℚ) (667 / 800 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_629 node_630
theorem node_627 : Covered ((333 / 400 : ℚ),(167 / 200 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (333 / 400 : ℚ) (167 / 200 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (667 / 800 : ℚ) node_628 node_633
theorem node_626 : Covered ((333 / 400 : ℚ),(167 / 200 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_625 : Covered ((333 / 400 : ℚ),(167 / 200 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (333 / 400 : ℚ) (167 / 200 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_626 node_627
theorem node_624 : Covered ((133 / 160 : ℚ),(333 / 400 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_623 : Covered ((133 / 160 : ℚ),(333 / 400 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_622 : Covered ((133 / 160 : ℚ),(333 / 400 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (133 / 160 : ℚ) (333 / 400 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_623 node_624
theorem node_621 : Covered ((83 / 100 : ℚ),(133 / 160 : ℚ)) ((111 / 3008 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_620 : Covered ((83 / 100 : ℚ),(133 / 160 : ℚ)) ((55 / 1504 : ℚ),(111 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_619 : Covered ((83 / 100 : ℚ),(133 / 160 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (133 / 160 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (111 / 3008 : ℚ) node_620 node_621
theorem node_618 : Covered ((83 / 100 : ℚ),(333 / 400 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (333 / 400 : ℚ) (55 / 1504 : ℚ) (7 / 188 : ℚ) (133 / 160 : ℚ) node_619 node_622
theorem node_617 : Covered ((83 / 100 : ℚ),(333 / 400 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_616 : Covered ((83 / 100 : ℚ),(333 / 400 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (333 / 400 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_617 node_618
theorem node_615 : Covered ((83 / 100 : ℚ),(167 / 200 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (167 / 200 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (333 / 400 : ℚ) node_616 node_625
theorem node_614 : Covered ((83 / 100 : ℚ),(167 / 200 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_613 : Covered ((83 / 100 : ℚ),(167 / 200 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (167 / 200 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_614 node_615
theorem node_612 : Covered ((83 / 100 : ℚ),(21 / 25 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (83 / 100 : ℚ) (21 / 25 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (167 / 200 : ℚ) node_613 node_642
theorem node_611 : Covered ((83 / 100 : ℚ),(21 / 25 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_610 : Covered ((83 / 100 : ℚ),(21 / 25 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (83 / 100 : ℚ) (21 / 25 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (13 / 376 : ℚ) node_611 node_612
theorem node_609 : Covered ((331 / 400 : ℚ),(83 / 100 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_608 : Covered ((331 / 400 : ℚ),(83 / 100 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_607 : Covered ((331 / 400 : ℚ),(83 / 100 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (331 / 400 : ℚ) (83 / 100 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_608 node_609
theorem node_606 : Covered ((33 / 40 : ℚ),(331 / 400 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_605 : Covered ((33 / 40 : ℚ),(331 / 400 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_604 : Covered ((33 / 40 : ℚ),(331 / 400 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (331 / 400 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_605 node_606
theorem node_603 : Covered ((33 / 40 : ℚ),(83 / 100 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (33 / 40 : ℚ) (83 / 100 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (331 / 400 : ℚ) node_604 node_607
theorem node_602 : Covered ((33 / 40 : ℚ),(83 / 100 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_601 : Covered ((33 / 40 : ℚ),(83 / 100 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (33 / 40 : ℚ) (83 / 100 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_602 node_603
theorem node_600 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((55 / 1504 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_599 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((27 / 752 : ℚ),(55 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_598 : Covered ((329 / 400 : ℚ),(33 / 40 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (329 / 400 : ℚ) (33 / 40 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (55 / 1504 : ℚ) node_599 node_600
theorem node_597 : Covered ((41 / 50 : ℚ),(329 / 400 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_596 : Covered ((41 / 50 : ℚ),(33 / 40 : ℚ)) ((27 / 752 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (33 / 40 : ℚ) (27 / 752 : ℚ) (7 / 188 : ℚ) (329 / 400 : ℚ) node_597 node_598
theorem node_595 : Covered ((41 / 50 : ℚ),(33 / 40 : ℚ)) ((13 / 376 : ℚ),(27 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_594 : Covered ((41 / 50 : ℚ),(33 / 40 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (33 / 40 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (27 / 752 : ℚ) node_595 node_596
theorem node_593 : Covered ((41 / 50 : ℚ),(83 / 100 : ℚ)) ((13 / 376 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (83 / 100 : ℚ) (13 / 376 : ℚ) (7 / 188 : ℚ) (33 / 40 : ℚ) node_594 node_601
theorem node_592 : Covered ((41 / 50 : ℚ),(83 / 100 : ℚ)) ((3 / 94 : ℚ),(13 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_591 : Covered ((41 / 50 : ℚ),(83 / 100 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (83 / 100 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (13 / 376 : ℚ) node_592 node_593
theorem node_590 : Covered ((41 / 50 : ℚ),(21 / 25 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 exact split_c (41 / 50 : ℚ) (21 / 25 : ℚ) (3 / 94 : ℚ) (7 / 188 : ℚ) (83 / 100 : ℚ) node_591 node_610
theorem node_589 : Covered ((41 / 50 : ℚ),(21 / 25 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (41 / 50 : ℚ) (21 / 25 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_590 node_781
theorem node_588 : Covered ((163 / 200 : ℚ),(41 / 50 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_587 : Covered ((81 / 100 : ℚ),(163 / 200 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_586 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_585 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_584 : Covered ((649 / 800 : ℚ),(13 / 16 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_583 : Covered ((81 / 100 : ℚ),(649 / 800 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_582 : Covered ((1297 / 1600 : ℚ),(649 / 800 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_581 : Covered ((81 / 100 : ℚ),(1297 / 1600 : ℚ)) ((241 / 6016 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_580 : Covered ((81 / 100 : ℚ),(1297 / 1600 : ℚ)) ((15 / 376 : ℚ),(241 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_579 : Covered ((81 / 100 : ℚ),(1297 / 1600 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (1297 / 1600 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (241 / 6016 : ℚ) node_580 node_581
theorem node_578 : Covered ((81 / 100 : ℚ),(649 / 800 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (649 / 800 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (1297 / 1600 : ℚ) node_579 node_582
theorem node_577 : Covered ((81 / 100 : ℚ),(649 / 800 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (649 / 800 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_578 node_583
theorem node_576 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (13 / 16 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (649 / 800 : ℚ) node_577 node_584
theorem node_575 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (13 / 16 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_576 node_585
theorem node_574 : Covered ((81 / 100 : ℚ),(163 / 200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (163 / 200 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (13 / 16 : ℚ) node_575 node_586
theorem node_573 : Covered ((81 / 100 : ℚ),(163 / 200 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (163 / 200 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_574 node_587
theorem node_572 : Covered ((81 / 100 : ℚ),(41 / 50 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (41 / 50 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (163 / 200 : ℚ) node_573 node_588
theorem node_571 : Covered ((327 / 400 : ℚ),(41 / 50 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_570 : Covered ((1311 / 1600 : ℚ),(41 / 50 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_569 : Covered ((2623 / 3200 : ℚ),(41 / 50 : ℚ)) ((469 / 12032 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_568 : Covered ((2623 / 3200 : ℚ),(41 / 50 : ℚ)) ((117 / 3008 : ℚ),(469 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_567 : Covered ((2623 / 3200 : ℚ),(41 / 50 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 exact split_j (2623 / 3200 : ℚ) (41 / 50 : ℚ) (117 / 3008 : ℚ) (5 / 128 : ℚ) (469 / 12032 : ℚ) node_568 node_569
theorem node_566 : Covered ((1311 / 1600 : ℚ),(2623 / 3200 : ℚ)) ((469 / 12032 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_565 : Covered ((1311 / 1600 : ℚ),(2623 / 3200 : ℚ)) ((117 / 3008 : ℚ),(469 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_564 : Covered ((1311 / 1600 : ℚ),(2623 / 3200 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 exact split_j (1311 / 1600 : ℚ) (2623 / 3200 : ℚ) (117 / 3008 : ℚ) (5 / 128 : ℚ) (469 / 12032 : ℚ) node_565 node_566
theorem node_563 : Covered ((1311 / 1600 : ℚ),(41 / 50 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 exact split_c (1311 / 1600 : ℚ) (41 / 50 : ℚ) (117 / 3008 : ℚ) (5 / 128 : ℚ) (2623 / 3200 : ℚ) node_564 node_567
theorem node_562 : Covered ((1311 / 1600 : ℚ),(41 / 50 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (1311 / 1600 : ℚ) (41 / 50 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (5 / 128 : ℚ) node_563 node_570
theorem node_561 : Covered ((131 / 160 : ℚ),(1311 / 1600 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_560 : Covered ((131 / 160 : ℚ),(1311 / 1600 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_559 : Covered ((131 / 160 : ℚ),(1311 / 1600 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (131 / 160 : ℚ) (1311 / 1600 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (5 / 128 : ℚ) node_560 node_561
theorem node_558 : Covered ((131 / 160 : ℚ),(41 / 50 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (131 / 160 : ℚ) (41 / 50 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (1311 / 1600 : ℚ) node_559 node_562
theorem node_557 : Covered ((1311 / 1600 : ℚ),(41 / 50 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_556 : Covered ((1311 / 1600 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_555 : Covered ((1311 / 1600 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (1311 / 1600 : ℚ) (41 / 50 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_556 node_557
theorem node_554 : Covered ((131 / 160 : ℚ),(1311 / 1600 : ℚ)) ((233 / 6016 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_553 : Covered ((131 / 160 : ℚ),(1311 / 1600 : ℚ)) ((29 / 752 : ℚ),(233 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_552 : Covered ((131 / 160 : ℚ),(1311 / 1600 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_j (131 / 160 : ℚ) (1311 / 1600 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (233 / 6016 : ℚ) node_553 node_554
theorem node_551 : Covered ((131 / 160 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 exact split_c (131 / 160 : ℚ) (41 / 50 : ℚ) (29 / 752 : ℚ) (117 / 3008 : ℚ) (1311 / 1600 : ℚ) node_552 node_555
theorem node_550 : Covered ((131 / 160 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (131 / 160 : ℚ) (41 / 50 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_551 node_558
theorem node_549 : Covered ((2619 / 3200 : ℚ),(131 / 160 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_548 : Covered ((1309 / 1600 : ℚ),(2619 / 3200 : ℚ)) ((471 / 12032 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_547 : Covered ((1309 / 1600 : ℚ),(2619 / 3200 : ℚ)) ((5 / 128 : ℚ),(471 / 12032 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_546 : Covered ((1309 / 1600 : ℚ),(2619 / 3200 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (1309 / 1600 : ℚ) (2619 / 3200 : ℚ) (5 / 128 : ℚ) (59 / 1504 : ℚ) (471 / 12032 : ℚ) node_547 node_548
theorem node_545 : Covered ((1309 / 1600 : ℚ),(131 / 160 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (1309 / 1600 : ℚ) (131 / 160 : ℚ) (5 / 128 : ℚ) (59 / 1504 : ℚ) (2619 / 3200 : ℚ) node_546 node_549
theorem node_544 : Covered ((1309 / 1600 : ℚ),(131 / 160 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_543 : Covered ((1309 / 1600 : ℚ),(131 / 160 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (1309 / 1600 : ℚ) (131 / 160 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (5 / 128 : ℚ) node_544 node_545
theorem node_542 : Covered ((2617 / 3200 : ℚ),(1309 / 1600 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_541 : Covered ((327 / 400 : ℚ),(2617 / 3200 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_540 : Covered ((327 / 400 : ℚ),(1309 / 1600 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (327 / 400 : ℚ) (1309 / 1600 : ℚ) (5 / 128 : ℚ) (59 / 1504 : ℚ) (2617 / 3200 : ℚ) node_541 node_542
theorem node_539 : Covered ((327 / 400 : ℚ),(1309 / 1600 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_538 : Covered ((327 / 400 : ℚ),(1309 / 1600 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (327 / 400 : ℚ) (1309 / 1600 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (5 / 128 : ℚ) node_539 node_540
theorem node_537 : Covered ((327 / 400 : ℚ),(131 / 160 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (327 / 400 : ℚ) (131 / 160 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (1309 / 1600 : ℚ) node_538 node_543
theorem node_536 : Covered ((327 / 400 : ℚ),(131 / 160 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_535 : Covered ((327 / 400 : ℚ),(131 / 160 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (327 / 400 : ℚ) (131 / 160 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_536 node_537
theorem node_534 : Covered ((327 / 400 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (327 / 400 : ℚ) (41 / 50 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (131 / 160 : ℚ) node_535 node_550
theorem node_533 : Covered ((327 / 400 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (327 / 400 : ℚ) (41 / 50 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_534 node_571
theorem node_532 : Covered ((653 / 800 : ℚ),(327 / 400 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_531 : Covered ((1307 / 1600 : ℚ),(327 / 400 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_530 : Covered ((653 / 800 : ℚ),(1307 / 1600 : ℚ)) ((237 / 6016 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_529 : Covered ((2613 / 3200 : ℚ),(1307 / 1600 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_528 : Covered ((653 / 800 : ℚ),(2613 / 3200 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_527 : Covered ((653 / 800 : ℚ),(1307 / 1600 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 exact split_c (653 / 800 : ℚ) (1307 / 1600 : ℚ) (59 / 1504 : ℚ) (237 / 6016 : ℚ) (2613 / 3200 : ℚ) node_528 node_529
theorem node_526 : Covered ((653 / 800 : ℚ),(1307 / 1600 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_j (653 / 800 : ℚ) (1307 / 1600 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (237 / 6016 : ℚ) node_527 node_530
theorem node_525 : Covered ((653 / 800 : ℚ),(327 / 400 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_c (653 / 800 : ℚ) (327 / 400 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (1307 / 1600 : ℚ) node_526 node_531
theorem node_524 : Covered ((653 / 800 : ℚ),(327 / 400 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (653 / 800 : ℚ) (327 / 400 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_525 node_532
theorem node_523 : Covered ((163 / 200 : ℚ),(653 / 800 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_522 : Covered ((261 / 320 : ℚ),(653 / 800 : ℚ)) ((237 / 6016 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_521 : Covered ((261 / 320 : ℚ),(653 / 800 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_520 : Covered ((261 / 320 : ℚ),(653 / 800 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_j (261 / 320 : ℚ) (653 / 800 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (237 / 6016 : ℚ) node_521 node_522
theorem node_519 : Covered ((163 / 200 : ℚ),(261 / 320 : ℚ)) ((237 / 6016 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_518 : Covered ((163 / 200 : ℚ),(261 / 320 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_517 : Covered ((163 / 200 : ℚ),(261 / 320 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_j (163 / 200 : ℚ) (261 / 320 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (237 / 6016 : ℚ) node_518 node_519
theorem node_516 : Covered ((163 / 200 : ℚ),(653 / 800 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_c (163 / 200 : ℚ) (653 / 800 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (261 / 320 : ℚ) node_517 node_520
theorem node_515 : Covered ((163 / 200 : ℚ),(653 / 800 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (163 / 200 : ℚ) (653 / 800 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_516 node_523
theorem node_514 : Covered ((163 / 200 : ℚ),(327 / 400 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (163 / 200 : ℚ) (327 / 400 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (653 / 800 : ℚ) node_515 node_524
theorem node_513 : Covered ((1307 / 1600 : ℚ),(327 / 400 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_512 : Covered ((1307 / 1600 : ℚ),(327 / 400 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_511 : Covered ((1307 / 1600 : ℚ),(327 / 400 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (1307 / 1600 : ℚ) (327 / 400 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (5 / 128 : ℚ) node_512 node_513
theorem node_510 : Covered ((653 / 800 : ℚ),(1307 / 1600 : ℚ)) ((5 / 128 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_509 : Covered ((653 / 800 : ℚ),(1307 / 1600 : ℚ)) ((117 / 3008 : ℚ),(5 / 128 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_508 : Covered ((653 / 800 : ℚ),(1307 / 1600 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (653 / 800 : ℚ) (1307 / 1600 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (5 / 128 : ℚ) node_509 node_510
theorem node_507 : Covered ((653 / 800 : ℚ),(327 / 400 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (653 / 800 : ℚ) (327 / 400 : ℚ) (117 / 3008 : ℚ) (59 / 1504 : ℚ) (1307 / 1600 : ℚ) node_508 node_511
theorem node_506 : Covered ((653 / 800 : ℚ),(327 / 400 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_505 : Covered ((653 / 800 : ℚ),(327 / 400 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (653 / 800 : ℚ) (327 / 400 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_506 node_507
theorem node_504 : Covered ((163 / 200 : ℚ),(653 / 800 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_503 : Covered ((163 / 200 : ℚ),(653 / 800 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_502 : Covered ((163 / 200 : ℚ),(653 / 800 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (163 / 200 : ℚ) (653 / 800 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_503 node_504
theorem node_501 : Covered ((163 / 200 : ℚ),(327 / 400 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (163 / 200 : ℚ) (327 / 400 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (653 / 800 : ℚ) node_502 node_505
theorem node_500 : Covered ((163 / 200 : ℚ),(327 / 400 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (163 / 200 : ℚ) (327 / 400 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_501 node_514
theorem node_499 : Covered ((163 / 200 : ℚ),(41 / 50 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (163 / 200 : ℚ) (41 / 50 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (327 / 400 : ℚ) node_500 node_533
theorem node_498 : Covered ((131 / 160 : ℚ),(41 / 50 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_497 : Covered ((131 / 160 : ℚ),(41 / 50 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_496 : Covered ((131 / 160 : ℚ),(41 / 50 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (131 / 160 : ℚ) (41 / 50 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_497 node_498
theorem node_495 : Covered ((327 / 400 : ℚ),(131 / 160 : ℚ)) ((115 / 3008 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_494 : Covered ((327 / 400 : ℚ),(131 / 160 : ℚ)) ((57 / 1504 : ℚ),(115 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_493 : Covered ((327 / 400 : ℚ),(131 / 160 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (327 / 400 : ℚ) (131 / 160 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (115 / 3008 : ℚ) node_494 node_495
theorem node_492 : Covered ((327 / 400 : ℚ),(41 / 50 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (327 / 400 : ℚ) (41 / 50 : ℚ) (57 / 1504 : ℚ) (29 / 752 : ℚ) (131 / 160 : ℚ) node_493 node_496
theorem node_491 : Covered ((327 / 400 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_490 : Covered ((327 / 400 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (327 / 400 : ℚ) (41 / 50 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_491 node_492
theorem node_489 : Covered ((163 / 200 : ℚ),(327 / 400 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_488 : Covered ((163 / 200 : ℚ),(327 / 400 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_487 : Covered ((163 / 200 : ℚ),(327 / 400 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (163 / 200 : ℚ) (327 / 400 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_488 node_489
theorem node_486 : Covered ((163 / 200 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (163 / 200 : ℚ) (41 / 50 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (327 / 400 : ℚ) node_487 node_490
theorem node_485 : Covered ((163 / 200 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (163 / 200 : ℚ) (41 / 50 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_486 node_499
theorem node_484 : Covered ((651 / 800 : ℚ),(163 / 200 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_483 : Covered ((1303 / 1600 : ℚ),(163 / 200 : ℚ)) ((237 / 6016 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_482 : Covered ((1303 / 1600 : ℚ),(163 / 200 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_481 : Covered ((1303 / 1600 : ℚ),(163 / 200 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_j (1303 / 1600 : ℚ) (163 / 200 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (237 / 6016 : ℚ) node_482 node_483
theorem node_480 : Covered ((651 / 800 : ℚ),(1303 / 1600 : ℚ)) ((237 / 6016 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_479 : Covered ((651 / 800 : ℚ),(1303 / 1600 : ℚ)) ((59 / 1504 : ℚ),(237 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_478 : Covered ((651 / 800 : ℚ),(1303 / 1600 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_j (651 / 800 : ℚ) (1303 / 1600 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (237 / 6016 : ℚ) node_479 node_480
theorem node_477 : Covered ((651 / 800 : ℚ),(163 / 200 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_c (651 / 800 : ℚ) (163 / 200 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (1303 / 1600 : ℚ) node_478 node_481
theorem node_476 : Covered ((651 / 800 : ℚ),(163 / 200 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (651 / 800 : ℚ) (163 / 200 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_477 node_484
theorem node_475 : Covered ((1301 / 1600 : ℚ),(651 / 800 : ℚ)) ((239 / 6016 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_474 : Covered ((1301 / 1600 : ℚ),(651 / 800 : ℚ)) ((119 / 3008 : ℚ),(239 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_473 : Covered ((1301 / 1600 : ℚ),(651 / 800 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (1301 / 1600 : ℚ) (651 / 800 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (239 / 6016 : ℚ) node_474 node_475
theorem node_472 : Covered ((13 / 16 : ℚ),(1301 / 1600 : ℚ)) ((239 / 6016 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_471 : Covered ((13 / 16 : ℚ),(1301 / 1600 : ℚ)) ((119 / 3008 : ℚ),(239 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_470 : Covered ((13 / 16 : ℚ),(1301 / 1600 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (13 / 16 : ℚ) (1301 / 1600 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (239 / 6016 : ℚ) node_471 node_472
theorem node_469 : Covered ((13 / 16 : ℚ),(651 / 800 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (13 / 16 : ℚ) (651 / 800 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (1301 / 1600 : ℚ) node_470 node_473
theorem node_468 : Covered ((1301 / 1600 : ℚ),(651 / 800 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_467 : Covered ((13 / 16 : ℚ),(1301 / 1600 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_466 : Covered ((13 / 16 : ℚ),(651 / 800 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 exact split_c (13 / 16 : ℚ) (651 / 800 : ℚ) (59 / 1504 : ℚ) (119 / 3008 : ℚ) (1301 / 1600 : ℚ) node_467 node_468
theorem node_465 : Covered ((13 / 16 : ℚ),(651 / 800 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (13 / 16 : ℚ) (651 / 800 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_466 node_469
theorem node_464 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (13 / 16 : ℚ) (163 / 200 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (651 / 800 : ℚ) node_465 node_476
theorem node_463 : Covered ((651 / 800 : ℚ),(163 / 200 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_462 : Covered ((651 / 800 : ℚ),(163 / 200 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_461 : Covered ((651 / 800 : ℚ),(163 / 200 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (651 / 800 : ℚ) (163 / 200 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_462 node_463
theorem node_460 : Covered ((13 / 16 : ℚ),(651 / 800 : ℚ)) ((117 / 3008 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_459 : Covered ((13 / 16 : ℚ),(651 / 800 : ℚ)) ((29 / 752 : ℚ),(117 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_458 : Covered ((13 / 16 : ℚ),(651 / 800 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_j (13 / 16 : ℚ) (651 / 800 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (117 / 3008 : ℚ) node_459 node_460
theorem node_457 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 exact split_c (13 / 16 : ℚ) (163 / 200 : ℚ) (29 / 752 : ℚ) (59 / 1504 : ℚ) (651 / 800 : ℚ) node_458 node_461
theorem node_456 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (13 / 16 : ℚ) (163 / 200 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_457 node_464
theorem node_455 : Covered ((1299 / 1600 : ℚ),(13 / 16 : ℚ)) ((239 / 6016 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_454 : Covered ((1299 / 1600 : ℚ),(13 / 16 : ℚ)) ((119 / 3008 : ℚ),(239 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_453 : Covered ((1299 / 1600 : ℚ),(13 / 16 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (1299 / 1600 : ℚ) (13 / 16 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (239 / 6016 : ℚ) node_454 node_455
theorem node_452 : Covered ((649 / 800 : ℚ),(1299 / 1600 : ℚ)) ((239 / 6016 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_451 : Covered ((649 / 800 : ℚ),(1299 / 1600 : ℚ)) ((119 / 3008 : ℚ),(239 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_450 : Covered ((649 / 800 : ℚ),(1299 / 1600 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (649 / 800 : ℚ) (1299 / 1600 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (239 / 6016 : ℚ) node_451 node_452
theorem node_449 : Covered ((649 / 800 : ℚ),(13 / 16 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (649 / 800 : ℚ) (13 / 16 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (1299 / 1600 : ℚ) node_450 node_453
theorem node_448 : Covered ((649 / 800 : ℚ),(13 / 16 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_447 : Covered ((649 / 800 : ℚ),(13 / 16 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (649 / 800 : ℚ) (13 / 16 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_448 node_449
theorem node_446 : Covered ((1297 / 1600 : ℚ),(649 / 800 : ℚ)) ((239 / 6016 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_445 : Covered ((1297 / 1600 : ℚ),(649 / 800 : ℚ)) ((119 / 3008 : ℚ),(239 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_444 : Covered ((1297 / 1600 : ℚ),(649 / 800 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (1297 / 1600 : ℚ) (649 / 800 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (239 / 6016 : ℚ) node_445 node_446
theorem node_443 : Covered ((81 / 100 : ℚ),(1297 / 1600 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_442 : Covered ((81 / 100 : ℚ),(649 / 800 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (649 / 800 : ℚ) (119 / 3008 : ℚ) (15 / 376 : ℚ) (1297 / 1600 : ℚ) node_443 node_444
theorem node_441 : Covered ((81 / 100 : ℚ),(649 / 800 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_440 : Covered ((81 / 100 : ℚ),(649 / 800 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (649 / 800 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_441 node_442
theorem node_439 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (13 / 16 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (649 / 800 : ℚ) node_440 node_447
theorem node_438 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_437 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (13 / 16 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_438 node_439
theorem node_436 : Covered ((81 / 100 : ℚ),(163 / 200 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (163 / 200 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (13 / 16 : ℚ) node_437 node_456
theorem node_435 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_434 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_433 : Covered ((13 / 16 : ℚ),(163 / 200 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (13 / 16 : ℚ) (163 / 200 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_434 node_435
theorem node_432 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((57 / 1504 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_431 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((7 / 188 : ℚ),(57 / 1504 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_430 : Covered ((81 / 100 : ℚ),(13 / 16 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (13 / 16 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (57 / 1504 : ℚ) node_431 node_432
theorem node_429 : Covered ((81 / 100 : ℚ),(163 / 200 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (163 / 200 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (13 / 16 : ℚ) node_430 node_433
theorem node_428 : Covered ((81 / 100 : ℚ),(163 / 200 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (163 / 200 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_429 node_436
theorem node_427 : Covered ((81 / 100 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (81 / 100 : ℚ) (41 / 50 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (163 / 200 : ℚ) node_428 node_485
theorem node_426 : Covered ((81 / 100 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (81 / 100 : ℚ) (41 / 50 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_427 node_572
theorem node_425 : Covered ((161 / 200 : ℚ),(81 / 100 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_424 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_423 : Covered ((647 / 800 : ℚ),(81 / 100 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_422 : Covered ((259 / 320 : ℚ),(81 / 100 : ℚ)) ((241 / 6016 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_421 : Covered ((259 / 320 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(241 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_420 : Covered ((259 / 320 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_j (259 / 320 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (241 / 6016 : ℚ) node_421 node_422
theorem node_419 : Covered ((647 / 800 : ℚ),(259 / 320 : ℚ)) ((241 / 6016 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_418 : Covered ((647 / 800 : ℚ),(259 / 320 : ℚ)) ((15 / 376 : ℚ),(241 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_417 : Covered ((647 / 800 : ℚ),(259 / 320 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_j (647 / 800 : ℚ) (259 / 320 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (241 / 6016 : ℚ) node_418 node_419
theorem node_416 : Covered ((647 / 800 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_c (647 / 800 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (259 / 320 : ℚ) node_417 node_420
theorem node_415 : Covered ((647 / 800 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (647 / 800 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_416 node_423
theorem node_414 : Covered ((323 / 400 : ℚ),(647 / 800 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_413 : Covered ((1293 / 1600 : ℚ),(647 / 800 : ℚ)) ((241 / 6016 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_412 : Covered ((1293 / 1600 : ℚ),(647 / 800 : ℚ)) ((15 / 376 : ℚ),(241 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_411 : Covered ((1293 / 1600 : ℚ),(647 / 800 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_j (1293 / 1600 : ℚ) (647 / 800 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (241 / 6016 : ℚ) node_412 node_413
theorem node_410 : Covered ((323 / 400 : ℚ),(1293 / 1600 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_409 : Covered ((323 / 400 : ℚ),(647 / 800 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 exact split_c (323 / 400 : ℚ) (647 / 800 : ℚ) (15 / 376 : ℚ) (121 / 3008 : ℚ) (1293 / 1600 : ℚ) node_410 node_411
theorem node_408 : Covered ((323 / 400 : ℚ),(647 / 800 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (323 / 400 : ℚ) (647 / 800 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_409 node_414
theorem node_407 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (323 / 400 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (647 / 800 : ℚ) node_408 node_415
theorem node_406 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (323 / 400 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_407 node_424
theorem node_405 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_404 : Covered ((1291 / 1600 : ℚ),(323 / 400 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_403 : Covered ((129 / 160 : ℚ),(1291 / 1600 : ℚ)) ((243 / 6016 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_402 : Covered ((129 / 160 : ℚ),(1291 / 1600 : ℚ)) ((121 / 3008 : ℚ),(243 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_401 : Covered ((129 / 160 : ℚ),(1291 / 1600 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (129 / 160 : ℚ) (1291 / 1600 : ℚ) (121 / 3008 : ℚ) (61 / 1504 : ℚ) (243 / 6016 : ℚ) node_402 node_403
theorem node_400 : Covered ((129 / 160 : ℚ),(323 / 400 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (129 / 160 : ℚ) (323 / 400 : ℚ) (121 / 3008 : ℚ) (61 / 1504 : ℚ) (1291 / 1600 : ℚ) node_401 node_404
theorem node_399 : Covered ((129 / 160 : ℚ),(323 / 400 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_398 : Covered ((129 / 160 : ℚ),(323 / 400 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (129 / 160 : ℚ) (323 / 400 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_399 node_400
theorem node_397 : Covered ((1289 / 1600 : ℚ),(129 / 160 : ℚ)) ((243 / 6016 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_396 : Covered ((1289 / 1600 : ℚ),(129 / 160 : ℚ)) ((121 / 3008 : ℚ),(243 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_395 : Covered ((1289 / 1600 : ℚ),(129 / 160 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (1289 / 1600 : ℚ) (129 / 160 : ℚ) (121 / 3008 : ℚ) (61 / 1504 : ℚ) (243 / 6016 : ℚ) node_396 node_397
theorem node_394 : Covered ((161 / 200 : ℚ),(1289 / 1600 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_393 : Covered ((161 / 200 : ℚ),(129 / 160 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (161 / 200 : ℚ) (129 / 160 : ℚ) (121 / 3008 : ℚ) (61 / 1504 : ℚ) (1289 / 1600 : ℚ) node_394 node_395
theorem node_392 : Covered ((161 / 200 : ℚ),(129 / 160 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_391 : Covered ((161 / 200 : ℚ),(129 / 160 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (161 / 200 : ℚ) (129 / 160 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_392 node_393
theorem node_390 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (161 / 200 : ℚ) (323 / 400 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (129 / 160 : ℚ) node_391 node_398
theorem node_389 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (161 / 200 : ℚ) (323 / 400 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_390 node_405
theorem node_388 : Covered ((161 / 200 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (161 / 200 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (323 / 400 : ℚ) node_389 node_406
theorem node_387 : Covered ((161 / 200 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (161 / 200 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_388 node_425
theorem node_386 : Covered ((4 / 5 : ℚ),(161 / 200 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_385 : Covered ((643 / 800 : ℚ),(161 / 200 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_384 : Covered ((321 / 400 : ℚ),(643 / 800 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_383 : Covered ((257 / 320 : ℚ),(643 / 800 : ℚ)) ((245 / 6016 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_382 : Covered ((257 / 320 : ℚ),(643 / 800 : ℚ)) ((61 / 1504 : ℚ),(245 / 6016 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_381 : Covered ((257 / 320 : ℚ),(643 / 800 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 exact split_j (257 / 320 : ℚ) (643 / 800 : ℚ) (61 / 1504 : ℚ) (123 / 3008 : ℚ) (245 / 6016 : ℚ) node_382 node_383
theorem node_380 : Covered ((321 / 400 : ℚ),(257 / 320 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_379 : Covered ((321 / 400 : ℚ),(643 / 800 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 exact split_c (321 / 400 : ℚ) (643 / 800 : ℚ) (61 / 1504 : ℚ) (123 / 3008 : ℚ) (257 / 320 : ℚ) node_380 node_381
theorem node_378 : Covered ((321 / 400 : ℚ),(643 / 800 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (321 / 400 : ℚ) (643 / 800 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_379 node_384
theorem node_377 : Covered ((321 / 400 : ℚ),(161 / 200 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (321 / 400 : ℚ) (161 / 200 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (643 / 800 : ℚ) node_378 node_385
theorem node_376 : Covered ((643 / 800 : ℚ),(161 / 200 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_375 : Covered ((643 / 800 : ℚ),(161 / 200 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_374 : Covered ((643 / 800 : ℚ),(161 / 200 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (643 / 800 : ℚ) (161 / 200 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_375 node_376
theorem node_373 : Covered ((321 / 400 : ℚ),(643 / 800 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_372 : Covered ((321 / 400 : ℚ),(643 / 800 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_371 : Covered ((321 / 400 : ℚ),(643 / 800 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (321 / 400 : ℚ) (643 / 800 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_372 node_373
theorem node_370 : Covered ((321 / 400 : ℚ),(161 / 200 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (321 / 400 : ℚ) (161 / 200 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (643 / 800 : ℚ) node_371 node_374
theorem node_369 : Covered ((321 / 400 : ℚ),(161 / 200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (321 / 400 : ℚ) (161 / 200 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_370 node_377
theorem node_368 : Covered ((641 / 800 : ℚ),(321 / 400 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_367 : Covered ((641 / 800 : ℚ),(321 / 400 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_366 : Covered ((641 / 800 : ℚ),(321 / 400 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (641 / 800 : ℚ) (321 / 400 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_367 node_368
theorem node_365 : Covered ((4 / 5 : ℚ),(641 / 800 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_364 : Covered ((4 / 5 : ℚ),(641 / 800 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_363 : Covered ((4 / 5 : ℚ),(641 / 800 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (641 / 800 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_364 node_365
theorem node_362 : Covered ((4 / 5 : ℚ),(321 / 400 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (321 / 400 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (641 / 800 : ℚ) node_363 node_366
theorem node_361 : Covered ((641 / 800 : ℚ),(321 / 400 : ℚ)) ((121 / 3008 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_360 : Covered ((641 / 800 : ℚ),(321 / 400 : ℚ)) ((15 / 376 : ℚ),(121 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_359 : Covered ((641 / 800 : ℚ),(321 / 400 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_j (641 / 800 : ℚ) (321 / 400 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (121 / 3008 : ℚ) node_360 node_361
theorem node_358 : Covered ((4 / 5 : ℚ),(641 / 800 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_357 : Covered ((4 / 5 : ℚ),(321 / 400 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (321 / 400 : ℚ) (15 / 376 : ℚ) (61 / 1504 : ℚ) (641 / 800 : ℚ) node_358 node_359
theorem node_356 : Covered ((4 / 5 : ℚ),(321 / 400 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (321 / 400 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_357 node_362
theorem node_355 : Covered ((4 / 5 : ℚ),(161 / 200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (161 / 200 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (321 / 400 : ℚ) node_356 node_369
theorem node_354 : Covered ((4 / 5 : ℚ),(161 / 200 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (161 / 200 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_355 node_386
theorem node_353 : Covered ((4 / 5 : ℚ),(81 / 100 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (81 / 100 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (161 / 200 : ℚ) node_354 node_387
theorem node_352 : Covered ((647 / 800 : ℚ),(81 / 100 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_351 : Covered ((647 / 800 : ℚ),(81 / 100 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_350 : Covered ((647 / 800 : ℚ),(81 / 100 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (647 / 800 : ℚ) (81 / 100 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_351 node_352
theorem node_349 : Covered ((323 / 400 : ℚ),(647 / 800 : ℚ)) ((119 / 3008 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_348 : Covered ((323 / 400 : ℚ),(647 / 800 : ℚ)) ((59 / 1504 : ℚ),(119 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_347 : Covered ((323 / 400 : ℚ),(647 / 800 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (323 / 400 : ℚ) (647 / 800 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (119 / 3008 : ℚ) node_348 node_349
theorem node_346 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (323 / 400 : ℚ) (81 / 100 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (647 / 800 : ℚ) node_347 node_350
theorem node_345 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_344 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (323 / 400 : ℚ) (81 / 100 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_345 node_346
theorem node_343 : Covered ((129 / 160 : ℚ),(323 / 400 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_342 : Covered ((161 / 200 : ℚ),(129 / 160 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_341 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (161 / 200 : ℚ) (323 / 400 : ℚ) (59 / 1504 : ℚ) (15 / 376 : ℚ) (129 / 160 : ℚ) node_342 node_343
theorem node_340 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_339 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (161 / 200 : ℚ) (323 / 400 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_340 node_341
theorem node_338 : Covered ((161 / 200 : ℚ),(81 / 100 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (161 / 200 : ℚ) (81 / 100 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (323 / 400 : ℚ) node_339 node_344
theorem node_337 : Covered ((323 / 400 : ℚ),(81 / 100 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_336 : Covered ((161 / 200 : ℚ),(323 / 400 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_335 : Covered ((161 / 200 : ℚ),(81 / 100 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 exact split_c (161 / 200 : ℚ) (81 / 100 : ℚ) (7 / 188 : ℚ) (29 / 752 : ℚ) (323 / 400 : ℚ) node_336 node_337
theorem node_334 : Covered ((161 / 200 : ℚ),(81 / 100 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (161 / 200 : ℚ) (81 / 100 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_335 node_338
theorem node_333 : Covered ((321 / 400 : ℚ),(161 / 200 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_332 : Covered ((321 / 400 : ℚ),(161 / 200 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_331 : Covered ((321 / 400 : ℚ),(161 / 200 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (321 / 400 : ℚ) (161 / 200 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_332 node_333
theorem node_330 : Covered ((4 / 5 : ℚ),(321 / 400 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_329 : Covered ((4 / 5 : ℚ),(321 / 400 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_328 : Covered ((4 / 5 : ℚ),(321 / 400 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (321 / 400 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_329 node_330
theorem node_327 : Covered ((4 / 5 : ℚ),(161 / 200 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (161 / 200 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (321 / 400 : ℚ) node_328 node_331
theorem node_326 : Covered ((4 / 5 : ℚ),(161 / 200 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_325 : Covered ((4 / 5 : ℚ),(161 / 200 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (161 / 200 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_326 node_327
theorem node_324 : Covered ((4 / 5 : ℚ),(81 / 100 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (81 / 100 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (161 / 200 : ℚ) node_325 node_334
theorem node_323 : Covered ((4 / 5 : ℚ),(81 / 100 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (81 / 100 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_324 node_353
theorem node_322 : Covered ((4 / 5 : ℚ),(41 / 50 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (41 / 50 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (81 / 100 : ℚ) node_323 node_426
theorem node_321 : Covered ((4 / 5 : ℚ),(41 / 50 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_320 : Covered ((4 / 5 : ℚ),(41 / 50 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (41 / 50 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_321 node_322
theorem node_319 : Covered ((4 / 5 : ℚ),(21 / 25 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (21 / 25 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (41 / 50 : ℚ) node_320 node_589
theorem node_318 : Covered ((4 / 5 : ℚ),(21 / 25 : ℚ)) ((1 / 47 : ℚ),(3 / 94 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_317 : Covered ((4 / 5 : ℚ),(21 / 25 : ℚ)) ((1 / 47 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (21 / 25 : ℚ) (1 / 47 : ℚ) (2 / 47 : ℚ) (3 / 94 : ℚ) node_318 node_319
theorem node_316 : Covered ((4 / 5 : ℚ),(22 / 25 : ℚ)) ((1 / 47 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (4 / 5 : ℚ) (22 / 25 : ℚ) (1 / 47 : ℚ) (2 / 47 : ℚ) (21 / 25 : ℚ) node_317 node_1156
theorem node_315 : Covered ((4 / 5 : ℚ),(22 / 25 : ℚ)) ((0 / 1 : ℚ),(1 / 47 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_314 : Covered ((4 / 5 : ℚ),(22 / 25 : ℚ)) ((0 / 1 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (4 / 5 : ℚ) (22 / 25 : ℚ) (0 / 1 : ℚ) (2 / 47 : ℚ) (1 / 47 : ℚ) node_315 node_316
theorem node_313 : Covered ((12767 / 16000 : ℚ),(4 / 5 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_312 : Covered ((51167 / 64000 : ℚ),(4 / 5 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_311 : Covered ((51167 / 64000 : ℚ),(4 / 5 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_310 : Covered ((51167 / 64000 : ℚ),(4 / 5 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (51167 / 64000 : ℚ) (4 / 5 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_311 node_312
theorem node_309 : Covered ((25567 / 32000 : ℚ),(51167 / 64000 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_308 : Covered ((25567 / 32000 : ℚ),(51167 / 64000 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_307 : Covered ((25567 / 32000 : ℚ),(51167 / 64000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25567 / 32000 : ℚ) (51167 / 64000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_308 node_309
theorem node_306 : Covered ((25567 / 32000 : ℚ),(4 / 5 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (25567 / 32000 : ℚ) (4 / 5 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (51167 / 64000 : ℚ) node_307 node_310
theorem node_305 : Covered ((25567 / 32000 : ℚ),(4 / 5 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_304 : Covered ((25567 / 32000 : ℚ),(4 / 5 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25567 / 32000 : ℚ) (4 / 5 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_305 node_306
theorem node_303 : Covered ((51101 / 64000 : ℚ),(25567 / 32000 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_302 : Covered ((51101 / 64000 : ℚ),(25567 / 32000 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_301 : Covered ((51101 / 64000 : ℚ),(25567 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (51101 / 64000 : ℚ) (25567 / 32000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_302 node_303
theorem node_300 : Covered ((12767 / 16000 : ℚ),(51101 / 64000 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_299 : Covered ((12767 / 16000 : ℚ),(51101 / 64000 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_298 : Covered ((12767 / 16000 : ℚ),(51101 / 64000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (12767 / 16000 : ℚ) (51101 / 64000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_299 node_300
theorem node_297 : Covered ((12767 / 16000 : ℚ),(25567 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (12767 / 16000 : ℚ) (25567 / 32000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (51101 / 64000 : ℚ) node_298 node_301
theorem node_296 : Covered ((12767 / 16000 : ℚ),(25567 / 32000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_295 : Covered ((12767 / 16000 : ℚ),(25567 / 32000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (12767 / 16000 : ℚ) (25567 / 32000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_296 node_297
theorem node_294 : Covered ((12767 / 16000 : ℚ),(4 / 5 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (12767 / 16000 : ℚ) (4 / 5 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (25567 / 32000 : ℚ) node_295 node_304
theorem node_293 : Covered ((12767 / 16000 : ℚ),(4 / 5 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12767 / 16000 : ℚ) (4 / 5 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_294 node_313
theorem node_292 : Covered ((25501 / 32000 : ℚ),(12767 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_291 : Covered ((6367 / 8000 : ℚ),(25501 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_290 : Covered ((50969 / 64000 : ℚ),(25501 / 32000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_289 : Covered ((50969 / 64000 : ℚ),(25501 / 32000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_288 : Covered ((50969 / 64000 : ℚ),(25501 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (50969 / 64000 : ℚ) (25501 / 32000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_289 node_290
theorem node_287 : Covered ((6367 / 8000 : ℚ),(50969 / 64000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_286 : Covered ((6367 / 8000 : ℚ),(50969 / 64000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_285 : Covered ((6367 / 8000 : ℚ),(50969 / 64000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (50969 / 64000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_286 node_287
theorem node_284 : Covered ((6367 / 8000 : ℚ),(25501 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (6367 / 8000 : ℚ) (25501 / 32000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (50969 / 64000 : ℚ) node_285 node_288
theorem node_283 : Covered ((6367 / 8000 : ℚ),(25501 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (25501 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_284 node_291
theorem node_282 : Covered ((6367 / 8000 : ℚ),(12767 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (6367 / 8000 : ℚ) (12767 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (25501 / 32000 : ℚ) node_283 node_292
theorem node_281 : Covered ((10207 / 12800 : ℚ),(12767 / 16000 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_280 : Covered ((10207 / 12800 : ℚ),(12767 / 16000 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_279 : Covered ((10207 / 12800 : ℚ),(12767 / 16000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (10207 / 12800 : ℚ) (12767 / 16000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_280 node_281
theorem node_278 : Covered ((25501 / 32000 : ℚ),(10207 / 12800 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_277 : Covered ((25501 / 32000 : ℚ),(10207 / 12800 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_276 : Covered ((25501 / 32000 : ℚ),(10207 / 12800 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25501 / 32000 : ℚ) (10207 / 12800 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_277 node_278
theorem node_275 : Covered ((25501 / 32000 : ℚ),(12767 / 16000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (25501 / 32000 : ℚ) (12767 / 16000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (10207 / 12800 : ℚ) node_276 node_279
theorem node_274 : Covered ((25501 / 32000 : ℚ),(12767 / 16000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_273 : Covered ((25501 / 32000 : ℚ),(12767 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25501 / 32000 : ℚ) (12767 / 16000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_274 node_275
theorem node_272 : Covered ((50969 / 64000 : ℚ),(25501 / 32000 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_271 : Covered ((50969 / 64000 : ℚ),(25501 / 32000 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_270 : Covered ((50969 / 64000 : ℚ),(25501 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (50969 / 64000 : ℚ) (25501 / 32000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_271 node_272
theorem node_269 : Covered ((6367 / 8000 : ℚ),(50969 / 64000 : ℚ)) ((123 / 3008 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_268 : Covered ((6367 / 8000 : ℚ),(50969 / 64000 : ℚ)) ((61 / 1504 : ℚ),(123 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_267 : Covered ((6367 / 8000 : ℚ),(50969 / 64000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (50969 / 64000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (123 / 3008 : ℚ) node_268 node_269
theorem node_266 : Covered ((6367 / 8000 : ℚ),(25501 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (6367 / 8000 : ℚ) (25501 / 32000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (50969 / 64000 : ℚ) node_267 node_270
theorem node_265 : Covered ((6367 / 8000 : ℚ),(25501 / 32000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_264 : Covered ((6367 / 8000 : ℚ),(25501 / 32000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (25501 / 32000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_265 node_266
theorem node_263 : Covered ((6367 / 8000 : ℚ),(12767 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (6367 / 8000 : ℚ) (12767 / 16000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (25501 / 32000 : ℚ) node_264 node_273
theorem node_262 : Covered ((6367 / 8000 : ℚ),(12767 / 16000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (12767 / 16000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_263 node_282
theorem node_261 : Covered ((6367 / 8000 : ℚ),(4 / 5 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (6367 / 8000 : ℚ) (4 / 5 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (12767 / 16000 : ℚ) node_262 node_293
theorem node_260 : Covered ((25567 / 32000 : ℚ),(4 / 5 : ℚ)) ((59 / 1504 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_259 : Covered ((25567 / 32000 : ℚ),(4 / 5 : ℚ)) ((29 / 752 : ℚ),(59 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_258 : Covered ((25567 / 32000 : ℚ),(4 / 5 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (25567 / 32000 : ℚ) (4 / 5 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (59 / 1504 : ℚ) node_259 node_260
theorem node_257 : Covered ((12767 / 16000 : ℚ),(25567 / 32000 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_256 : Covered ((12767 / 16000 : ℚ),(4 / 5 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (12767 / 16000 : ℚ) (4 / 5 : ℚ) (29 / 752 : ℚ) (15 / 376 : ℚ) (25567 / 32000 : ℚ) node_257 node_258
theorem node_255 : Covered ((12767 / 16000 : ℚ),(4 / 5 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_254 : Covered ((12767 / 16000 : ℚ),(4 / 5 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (12767 / 16000 : ℚ) (4 / 5 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_255 node_256
theorem node_253 : Covered ((6367 / 8000 : ℚ),(12767 / 16000 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_252 : Covered ((6367 / 8000 : ℚ),(12767 / 16000 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_251 : Covered ((6367 / 8000 : ℚ),(12767 / 16000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (12767 / 16000 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_252 node_253
theorem node_250 : Covered ((6367 / 8000 : ℚ),(4 / 5 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (6367 / 8000 : ℚ) (4 / 5 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (12767 / 16000 : ℚ) node_251 node_254
theorem node_249 : Covered ((6367 / 8000 : ℚ),(4 / 5 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6367 / 8000 : ℚ) (4 / 5 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_250 node_261
theorem node_248 : Covered ((5087 / 6400 : ℚ),(6367 / 8000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_247 : Covered ((50903 / 64000 : ℚ),(6367 / 8000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_246 : Covered ((50903 / 64000 : ℚ),(6367 / 8000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_245 : Covered ((50903 / 64000 : ℚ),(6367 / 8000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (50903 / 64000 : ℚ) (6367 / 8000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_246 node_247
theorem node_244 : Covered ((5087 / 6400 : ℚ),(50903 / 64000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_243 : Covered ((5087 / 6400 : ℚ),(50903 / 64000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_242 : Covered ((5087 / 6400 : ℚ),(50903 / 64000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (5087 / 6400 : ℚ) (50903 / 64000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_243 node_244
theorem node_241 : Covered ((5087 / 6400 : ℚ),(6367 / 8000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (5087 / 6400 : ℚ) (6367 / 8000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (50903 / 64000 : ℚ) node_242 node_245
theorem node_240 : Covered ((5087 / 6400 : ℚ),(6367 / 8000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (5087 / 6400 : ℚ) (6367 / 8000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_241 node_248
theorem node_239 : Covered ((12701 / 16000 : ℚ),(5087 / 6400 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_238 : Covered ((50837 / 64000 : ℚ),(5087 / 6400 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_237 : Covered ((50837 / 64000 : ℚ),(5087 / 6400 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_236 : Covered ((50837 / 64000 : ℚ),(5087 / 6400 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (50837 / 64000 : ℚ) (5087 / 6400 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_237 node_238
theorem node_235 : Covered ((12701 / 16000 : ℚ),(50837 / 64000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_234 : Covered ((12701 / 16000 : ℚ),(50837 / 64000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_233 : Covered ((12701 / 16000 : ℚ),(50837 / 64000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (12701 / 16000 : ℚ) (50837 / 64000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_234 node_235
theorem node_232 : Covered ((12701 / 16000 : ℚ),(5087 / 6400 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (12701 / 16000 : ℚ) (5087 / 6400 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (50837 / 64000 : ℚ) node_233 node_236
theorem node_231 : Covered ((12701 / 16000 : ℚ),(5087 / 6400 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12701 / 16000 : ℚ) (5087 / 6400 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_232 node_239
theorem node_230 : Covered ((12701 / 16000 : ℚ),(6367 / 8000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (12701 / 16000 : ℚ) (6367 / 8000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (5087 / 6400 : ℚ) node_231 node_240
theorem node_229 : Covered ((50903 / 64000 : ℚ),(6367 / 8000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_228 : Covered ((5087 / 6400 : ℚ),(50903 / 64000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_227 : Covered ((5087 / 6400 : ℚ),(6367 / 8000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (5087 / 6400 : ℚ) (6367 / 8000 : ℚ) (61 / 1504 : ℚ) (31 / 752 : ℚ) (50903 / 64000 : ℚ) node_228 node_229
theorem node_226 : Covered ((5087 / 6400 : ℚ),(6367 / 8000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_225 : Covered ((5087 / 6400 : ℚ),(6367 / 8000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (5087 / 6400 : ℚ) (6367 / 8000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_226 node_227
theorem node_224 : Covered ((12701 / 16000 : ℚ),(5087 / 6400 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_223 : Covered ((12701 / 16000 : ℚ),(5087 / 6400 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_222 : Covered ((12701 / 16000 : ℚ),(5087 / 6400 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (12701 / 16000 : ℚ) (5087 / 6400 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_223 node_224
theorem node_221 : Covered ((12701 / 16000 : ℚ),(6367 / 8000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (12701 / 16000 : ℚ) (6367 / 8000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (5087 / 6400 : ℚ) node_222 node_225
theorem node_220 : Covered ((12701 / 16000 : ℚ),(6367 / 8000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12701 / 16000 : ℚ) (6367 / 8000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_221 node_230
theorem node_219 : Covered ((25369 / 32000 : ℚ),(12701 / 16000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_218 : Covered ((50771 / 64000 : ℚ),(12701 / 16000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_217 : Covered ((50771 / 64000 : ℚ),(12701 / 16000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_216 : Covered ((50771 / 64000 : ℚ),(12701 / 16000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (50771 / 64000 : ℚ) (12701 / 16000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_217 node_218
theorem node_215 : Covered ((25369 / 32000 : ℚ),(50771 / 64000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_214 : Covered ((25369 / 32000 : ℚ),(50771 / 64000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_213 : Covered ((25369 / 32000 : ℚ),(50771 / 64000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (25369 / 32000 : ℚ) (50771 / 64000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_214 node_215
theorem node_212 : Covered ((25369 / 32000 : ℚ),(12701 / 16000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (25369 / 32000 : ℚ) (12701 / 16000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (50771 / 64000 : ℚ) node_213 node_216
theorem node_211 : Covered ((25369 / 32000 : ℚ),(12701 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25369 / 32000 : ℚ) (12701 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_212 node_219
theorem node_210 : Covered ((3167 / 4000 : ℚ),(25369 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_209 : Covered ((10141 / 12800 : ℚ),(25369 / 32000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_208 : Covered ((10141 / 12800 : ℚ),(25369 / 32000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_207 : Covered ((10141 / 12800 : ℚ),(25369 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (10141 / 12800 : ℚ) (25369 / 32000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_208 node_209
theorem node_206 : Covered ((3167 / 4000 : ℚ),(10141 / 12800 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_205 : Covered ((3167 / 4000 : ℚ),(10141 / 12800 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_204 : Covered ((3167 / 4000 : ℚ),(10141 / 12800 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (10141 / 12800 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_205 node_206
theorem node_203 : Covered ((3167 / 4000 : ℚ),(25369 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (3167 / 4000 : ℚ) (25369 / 32000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (10141 / 12800 : ℚ) node_204 node_207
theorem node_202 : Covered ((3167 / 4000 : ℚ),(25369 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (25369 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_203 node_210
theorem node_201 : Covered ((3167 / 4000 : ℚ),(12701 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (3167 / 4000 : ℚ) (12701 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (25369 / 32000 : ℚ) node_202 node_211
theorem node_200 : Covered ((25369 / 32000 : ℚ),(12701 / 16000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_199 : Covered ((25369 / 32000 : ℚ),(12701 / 16000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_198 : Covered ((25369 / 32000 : ℚ),(12701 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25369 / 32000 : ℚ) (12701 / 16000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_199 node_200
theorem node_197 : Covered ((3167 / 4000 : ℚ),(25369 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_196 : Covered ((3167 / 4000 : ℚ),(25369 / 32000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_195 : Covered ((3167 / 4000 : ℚ),(25369 / 32000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (25369 / 32000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_196 node_197
theorem node_194 : Covered ((3167 / 4000 : ℚ),(12701 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (3167 / 4000 : ℚ) (12701 / 16000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (25369 / 32000 : ℚ) node_195 node_198
theorem node_193 : Covered ((3167 / 4000 : ℚ),(12701 / 16000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (12701 / 16000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_194 node_201
theorem node_192 : Covered ((3167 / 4000 : ℚ),(6367 / 8000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (3167 / 4000 : ℚ) (6367 / 8000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (12701 / 16000 : ℚ) node_193 node_220
theorem node_191 : Covered ((12701 / 16000 : ℚ),(6367 / 8000 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_190 : Covered ((12701 / 16000 : ℚ),(6367 / 8000 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_189 : Covered ((12701 / 16000 : ℚ),(6367 / 8000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (12701 / 16000 : ℚ) (6367 / 8000 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_190 node_191
theorem node_188 : Covered ((3167 / 4000 : ℚ),(12701 / 16000 : ℚ)) ((29 / 752 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_187 : Covered ((3167 / 4000 : ℚ),(12701 / 16000 : ℚ)) ((7 / 188 : ℚ),(29 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_186 : Covered ((3167 / 4000 : ℚ),(12701 / 16000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (12701 / 16000 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (29 / 752 : ℚ) node_187 node_188
theorem node_185 : Covered ((3167 / 4000 : ℚ),(6367 / 8000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 exact split_c (3167 / 4000 : ℚ) (6367 / 8000 : ℚ) (7 / 188 : ℚ) (15 / 376 : ℚ) (12701 / 16000 : ℚ) node_186 node_189
theorem node_184 : Covered ((3167 / 4000 : ℚ),(6367 / 8000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (6367 / 8000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_185 node_192
theorem node_183 : Covered ((3167 / 4000 : ℚ),(4 / 5 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (3167 / 4000 : ℚ) (4 / 5 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (6367 / 8000 : ℚ) node_184 node_249
theorem node_182 : Covered ((3167 / 4000 : ℚ),(4 / 5 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_181 : Covered ((3167 / 4000 : ℚ),(4 / 5 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3167 / 4000 : ℚ) (4 / 5 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_182 node_183
theorem node_180 : Covered ((50639 / 64000 : ℚ),(3167 / 4000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_179 : Covered ((25303 / 32000 : ℚ),(50639 / 64000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_178 : Covered ((25303 / 32000 : ℚ),(50639 / 64000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (1 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_177 : Covered ((25303 / 32000 : ℚ),(50639 / 64000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25303 / 32000 : ℚ) (50639 / 64000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_178 node_179
theorem node_176 : Covered ((25303 / 32000 : ℚ),(3167 / 4000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (25303 / 32000 : ℚ) (3167 / 4000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (50639 / 64000 : ℚ) node_177 node_180
theorem node_175 : Covered ((50639 / 64000 : ℚ),(3167 / 4000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_174 : Covered ((50639 / 64000 : ℚ),(3167 / 4000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_173 : Covered ((50639 / 64000 : ℚ),(3167 / 4000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (50639 / 64000 : ℚ) (3167 / 4000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_174 node_175
theorem node_172 : Covered ((25303 / 32000 : ℚ),(50639 / 64000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_171 : Covered ((25303 / 32000 : ℚ),(50639 / 64000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_170 : Covered ((25303 / 32000 : ℚ),(50639 / 64000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (25303 / 32000 : ℚ) (50639 / 64000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_171 node_172
theorem node_169 : Covered ((25303 / 32000 : ℚ),(3167 / 4000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (25303 / 32000 : ℚ) (3167 / 4000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (50639 / 64000 : ℚ) node_170 node_173
theorem node_168 : Covered ((25303 / 32000 : ℚ),(3167 / 4000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25303 / 32000 : ℚ) (3167 / 4000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_169 node_176
theorem node_167 : Covered ((50573 / 64000 : ℚ),(25303 / 32000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_166 : Covered ((50573 / 64000 : ℚ),(25303 / 32000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_165 : Covered ((50573 / 64000 : ℚ),(25303 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (50573 / 64000 : ℚ) (25303 / 32000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_166 node_167
theorem node_164 : Covered ((2527 / 3200 : ℚ),(50573 / 64000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_163 : Covered ((2527 / 3200 : ℚ),(50573 / 64000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_162 : Covered ((2527 / 3200 : ℚ),(50573 / 64000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (2527 / 3200 : ℚ) (50573 / 64000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_163 node_164
theorem node_161 : Covered ((2527 / 3200 : ℚ),(25303 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (2527 / 3200 : ℚ) (25303 / 32000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (50573 / 64000 : ℚ) node_162 node_165
theorem node_160 : Covered ((50573 / 64000 : ℚ),(25303 / 32000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_159 : Covered ((50573 / 64000 : ℚ),(25303 / 32000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_158 : Covered ((50573 / 64000 : ℚ),(25303 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (50573 / 64000 : ℚ) (25303 / 32000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_159 node_160
theorem node_157 : Covered ((2527 / 3200 : ℚ),(50573 / 64000 : ℚ)) ((125 / 3008 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_156 : Covered ((2527 / 3200 : ℚ),(50573 / 64000 : ℚ)) ((31 / 752 : ℚ),(125 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_155 : Covered ((2527 / 3200 : ℚ),(50573 / 64000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_j (2527 / 3200 : ℚ) (50573 / 64000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (125 / 3008 : ℚ) node_156 node_157
theorem node_154 : Covered ((2527 / 3200 : ℚ),(25303 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 exact split_c (2527 / 3200 : ℚ) (25303 / 32000 : ℚ) (31 / 752 : ℚ) (63 / 1504 : ℚ) (50573 / 64000 : ℚ) node_155 node_158
theorem node_153 : Covered ((2527 / 3200 : ℚ),(25303 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (2527 / 3200 : ℚ) (25303 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_154 node_161
theorem node_152 : Covered ((2527 / 3200 : ℚ),(3167 / 4000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (2527 / 3200 : ℚ) (3167 / 4000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (25303 / 32000 : ℚ) node_153 node_168
theorem node_151 : Covered ((25303 / 32000 : ℚ),(3167 / 4000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_150 : Covered ((25303 / 32000 : ℚ),(3167 / 4000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_149 : Covered ((25303 / 32000 : ℚ),(3167 / 4000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25303 / 32000 : ℚ) (3167 / 4000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_150 node_151
theorem node_148 : Covered ((2527 / 3200 : ℚ),(25303 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_147 : Covered ((2527 / 3200 : ℚ),(25303 / 32000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_146 : Covered ((2527 / 3200 : ℚ),(25303 / 32000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (2527 / 3200 : ℚ) (25303 / 32000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_147 node_148
theorem node_145 : Covered ((2527 / 3200 : ℚ),(3167 / 4000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (2527 / 3200 : ℚ) (3167 / 4000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (25303 / 32000 : ℚ) node_146 node_149
theorem node_144 : Covered ((2527 / 3200 : ℚ),(3167 / 4000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (2527 / 3200 : ℚ) (3167 / 4000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_145 node_152
theorem node_143 : Covered ((50507 / 64000 : ℚ),(2527 / 3200 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_142 : Covered ((50507 / 64000 : ℚ),(2527 / 3200 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_141 : Covered ((50507 / 64000 : ℚ),(2527 / 3200 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (50507 / 64000 : ℚ) (2527 / 3200 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_142 node_143
theorem node_140 : Covered ((25237 / 32000 : ℚ),(50507 / 64000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_139 : Covered ((25237 / 32000 : ℚ),(50507 / 64000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_138 : Covered ((25237 / 32000 : ℚ),(50507 / 64000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25237 / 32000 : ℚ) (50507 / 64000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_139 node_140
theorem node_137 : Covered ((25237 / 32000 : ℚ),(2527 / 3200 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (25237 / 32000 : ℚ) (2527 / 3200 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (50507 / 64000 : ℚ) node_138 node_141
theorem node_136 : Covered ((25237 / 32000 : ℚ),(2527 / 3200 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_135 : Covered ((25237 / 32000 : ℚ),(2527 / 3200 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25237 / 32000 : ℚ) (2527 / 3200 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_136 node_137
theorem node_134 : Covered ((50441 / 64000 : ℚ),(25237 / 32000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_133 : Covered ((50441 / 64000 : ℚ),(25237 / 32000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_132 : Covered ((50441 / 64000 : ℚ),(25237 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (50441 / 64000 : ℚ) (25237 / 32000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_133 node_134
theorem node_131 : Covered ((6301 / 8000 : ℚ),(50441 / 64000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_130 : Covered ((6301 / 8000 : ℚ),(50441 / 64000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_129 : Covered ((6301 / 8000 : ℚ),(50441 / 64000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6301 / 8000 : ℚ) (50441 / 64000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_130 node_131
theorem node_128 : Covered ((6301 / 8000 : ℚ),(25237 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (6301 / 8000 : ℚ) (25237 / 32000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (50441 / 64000 : ℚ) node_129 node_132
theorem node_127 : Covered ((6301 / 8000 : ℚ),(25237 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_126 : Covered ((6301 / 8000 : ℚ),(25237 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6301 / 8000 : ℚ) (25237 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_127 node_128
theorem node_125 : Covered ((6301 / 8000 : ℚ),(2527 / 3200 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (6301 / 8000 : ℚ) (2527 / 3200 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (25237 / 32000 : ℚ) node_126 node_135
theorem node_124 : Covered ((25237 / 32000 : ℚ),(2527 / 3200 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_123 : Covered ((25237 / 32000 : ℚ),(2527 / 3200 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_122 : Covered ((25237 / 32000 : ℚ),(2527 / 3200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (25237 / 32000 : ℚ) (2527 / 3200 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_123 node_124
theorem node_121 : Covered ((6301 / 8000 : ℚ),(25237 / 32000 : ℚ)) ((61 / 1504 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_120 : Covered ((6301 / 8000 : ℚ),(25237 / 32000 : ℚ)) ((15 / 376 : ℚ),(61 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_119 : Covered ((6301 / 8000 : ℚ),(25237 / 32000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_j (6301 / 8000 : ℚ) (25237 / 32000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (61 / 1504 : ℚ) node_120 node_121
theorem node_118 : Covered ((6301 / 8000 : ℚ),(2527 / 3200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (6301 / 8000 : ℚ) (2527 / 3200 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (25237 / 32000 : ℚ) node_119 node_122
theorem node_117 : Covered ((6301 / 8000 : ℚ),(2527 / 3200 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6301 / 8000 : ℚ) (2527 / 3200 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_118 node_125
theorem node_116 : Covered ((6301 / 8000 : ℚ),(3167 / 4000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (6301 / 8000 : ℚ) (3167 / 4000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (2527 / 3200 : ℚ) node_117 node_144
theorem node_115 : Covered ((6301 / 8000 : ℚ),(3167 / 4000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_114 : Covered ((6301 / 8000 : ℚ),(3167 / 4000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6301 / 8000 : ℚ) (3167 / 4000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_115 node_116
theorem node_113 : Covered ((403 / 512 : ℚ),(6301 / 8000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_112 : Covered ((403 / 512 : ℚ),(6301 / 8000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_111 : Covered ((403 / 512 : ℚ),(6301 / 8000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (403 / 512 : ℚ) (6301 / 8000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_112 node_113
theorem node_110 : Covered ((25171 / 32000 : ℚ),(403 / 512 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_109 : Covered ((25171 / 32000 : ℚ),(403 / 512 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_108 : Covered ((25171 / 32000 : ℚ),(403 / 512 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25171 / 32000 : ℚ) (403 / 512 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_109 node_110
theorem node_107 : Covered ((25171 / 32000 : ℚ),(6301 / 8000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (25171 / 32000 : ℚ) (6301 / 8000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (403 / 512 : ℚ) node_108 node_111
theorem node_106 : Covered ((25171 / 32000 : ℚ),(6301 / 8000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_105 : Covered ((25171 / 32000 : ℚ),(6301 / 8000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25171 / 32000 : ℚ) (6301 / 8000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_106 node_107
theorem node_104 : Covered ((50309 / 64000 : ℚ),(25171 / 32000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_103 : Covered ((50309 / 64000 : ℚ),(25171 / 32000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_102 : Covered ((50309 / 64000 : ℚ),(25171 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (50309 / 64000 : ℚ) (25171 / 32000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_103 node_104
theorem node_101 : Covered ((12569 / 16000 : ℚ),(50309 / 64000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_100 : Covered ((12569 / 16000 : ℚ),(50309 / 64000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_99 : Covered ((12569 / 16000 : ℚ),(50309 / 64000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12569 / 16000 : ℚ) (50309 / 64000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_100 node_101
theorem node_98 : Covered ((12569 / 16000 : ℚ),(25171 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (12569 / 16000 : ℚ) (25171 / 32000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (50309 / 64000 : ℚ) node_99 node_102
theorem node_97 : Covered ((12569 / 16000 : ℚ),(25171 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_96 : Covered ((12569 / 16000 : ℚ),(25171 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12569 / 16000 : ℚ) (25171 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_97 node_98
theorem node_95 : Covered ((12569 / 16000 : ℚ),(6301 / 8000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (12569 / 16000 : ℚ) (6301 / 8000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (25171 / 32000 : ℚ) node_96 node_105
theorem node_94 : Covered ((25171 / 32000 : ℚ),(6301 / 8000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_93 : Covered ((12569 / 16000 : ℚ),(25171 / 32000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_92 : Covered ((12569 / 16000 : ℚ),(6301 / 8000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 exact split_c (12569 / 16000 : ℚ) (6301 / 8000 : ℚ) (15 / 376 : ℚ) (31 / 752 : ℚ) (25171 / 32000 : ℚ) node_93 node_94
theorem node_91 : Covered ((12569 / 16000 : ℚ),(6301 / 8000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12569 / 16000 : ℚ) (6301 / 8000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_92 node_95
theorem node_90 : Covered ((50243 / 64000 : ℚ),(12569 / 16000 : ℚ)) ((127 / 3008 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_89 : Covered ((50243 / 64000 : ℚ),(12569 / 16000 : ℚ)) ((63 / 1504 : ℚ),(127 / 3008 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_88 : Covered ((50243 / 64000 : ℚ),(12569 / 16000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (50243 / 64000 : ℚ) (12569 / 16000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (127 / 3008 : ℚ) node_89 node_90
theorem node_87 : Covered ((5021 / 6400 : ℚ),(50243 / 64000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_86 : Covered ((5021 / 6400 : ℚ),(12569 / 16000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (5021 / 6400 : ℚ) (12569 / 16000 : ℚ) (63 / 1504 : ℚ) (2 / 47 : ℚ) (50243 / 64000 : ℚ) node_87 node_88
theorem node_85 : Covered ((5021 / 6400 : ℚ),(12569 / 16000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_84 : Covered ((5021 / 6400 : ℚ),(12569 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (5021 / 6400 : ℚ) (12569 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_85 node_86
theorem node_83 : Covered ((1567 / 2000 : ℚ),(5021 / 6400 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_82 : Covered ((1567 / 2000 : ℚ),(5021 / 6400 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_81 : Covered ((1567 / 2000 : ℚ),(5021 / 6400 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1567 / 2000 : ℚ) (5021 / 6400 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_82 node_83
theorem node_80 : Covered ((1567 / 2000 : ℚ),(12569 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (1567 / 2000 : ℚ) (12569 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (5021 / 6400 : ℚ) node_81 node_84
theorem node_79 : Covered ((1567 / 2000 : ℚ),(12569 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_78 : Covered ((1567 / 2000 : ℚ),(12569 / 16000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1567 / 2000 : ℚ) (12569 / 16000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_79 node_80
theorem node_77 : Covered ((1567 / 2000 : ℚ),(6301 / 8000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (1567 / 2000 : ℚ) (6301 / 8000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (12569 / 16000 : ℚ) node_78 node_91
theorem node_76 : Covered ((1567 / 2000 : ℚ),(6301 / 8000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_75 : Covered ((1567 / 2000 : ℚ),(6301 / 8000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1567 / 2000 : ℚ) (6301 / 8000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_76 node_77
theorem node_74 : Covered ((1567 / 2000 : ℚ),(3167 / 4000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (1567 / 2000 : ℚ) (3167 / 4000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (6301 / 8000 : ℚ) node_75 node_114
theorem node_73 : Covered ((1567 / 2000 : ℚ),(3167 / 4000 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_72 : Covered ((1567 / 2000 : ℚ),(3167 / 4000 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1567 / 2000 : ℚ) (3167 / 4000 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_73 node_74
theorem node_71 : Covered ((1567 / 2000 : ℚ),(4 / 5 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (1567 / 2000 : ℚ) (4 / 5 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (3167 / 4000 : ℚ) node_72 node_181
theorem node_70 : Covered ((1567 / 2000 : ℚ),(4 / 5 : ℚ)) ((1 / 47 : ℚ),(3 / 94 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_69 : Covered ((1567 / 2000 : ℚ),(4 / 5 : ℚ)) ((1 / 47 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1567 / 2000 : ℚ) (4 / 5 : ℚ) (1 / 47 : ℚ) (2 / 47 : ℚ) (3 / 94 : ℚ) node_70 node_71
theorem node_68 : Covered ((25039 / 32000 : ℚ),(1567 / 2000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_67 : Covered ((25039 / 32000 : ℚ),(1567 / 2000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_66 : Covered ((25039 / 32000 : ℚ),(1567 / 2000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (25039 / 32000 : ℚ) (1567 / 2000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_67 node_68
theorem node_65 : Covered ((12503 / 16000 : ℚ),(25039 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_64 : Covered ((12503 / 16000 : ℚ),(25039 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_63 : Covered ((12503 / 16000 : ℚ),(25039 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12503 / 16000 : ℚ) (25039 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_64 node_65
theorem node_62 : Covered ((12503 / 16000 : ℚ),(1567 / 2000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (12503 / 16000 : ℚ) (1567 / 2000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (25039 / 32000 : ℚ) node_63 node_66
theorem node_61 : Covered ((12503 / 16000 : ℚ),(1567 / 2000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_60 : Covered ((12503 / 16000 : ℚ),(1567 / 2000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12503 / 16000 : ℚ) (1567 / 2000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_61 node_62
theorem node_59 : Covered ((24973 / 32000 : ℚ),(12503 / 16000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_58 : Covered ((24973 / 32000 : ℚ),(12503 / 16000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_57 : Covered ((24973 / 32000 : ℚ),(12503 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (24973 / 32000 : ℚ) (12503 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_58 node_59
theorem node_56 : Covered ((1247 / 1600 : ℚ),(24973 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_55 : Covered ((1247 / 1600 : ℚ),(24973 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_54 : Covered ((1247 / 1600 : ℚ),(24973 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1247 / 1600 : ℚ) (24973 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_55 node_56
theorem node_53 : Covered ((1247 / 1600 : ℚ),(12503 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (1247 / 1600 : ℚ) (12503 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (24973 / 32000 : ℚ) node_54 node_57
theorem node_52 : Covered ((1247 / 1600 : ℚ),(12503 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_51 : Covered ((1247 / 1600 : ℚ),(12503 / 16000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1247 / 1600 : ℚ) (12503 / 16000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_52 node_53
theorem node_50 : Covered ((1247 / 1600 : ℚ),(1567 / 2000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (1247 / 1600 : ℚ) (1567 / 2000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (12503 / 16000 : ℚ) node_51 node_60
theorem node_49 : Covered ((1247 / 1600 : ℚ),(1567 / 2000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_48 : Covered ((1247 / 1600 : ℚ),(1567 / 2000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (1247 / 1600 : ℚ) (1567 / 2000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_49 node_50
theorem node_47 : Covered ((24907 / 32000 : ℚ),(1247 / 1600 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_46 : Covered ((24907 / 32000 : ℚ),(1247 / 1600 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_45 : Covered ((24907 / 32000 : ℚ),(1247 / 1600 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (24907 / 32000 : ℚ) (1247 / 1600 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_46 node_47
theorem node_44 : Covered ((12437 / 16000 : ℚ),(24907 / 32000 : ℚ)) ((63 / 1504 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_43 : Covered ((12437 / 16000 : ℚ),(24907 / 32000 : ℚ)) ((31 / 752 : ℚ),(63 / 1504 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_42 : Covered ((12437 / 16000 : ℚ),(24907 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12437 / 16000 : ℚ) (24907 / 32000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (63 / 1504 : ℚ) node_43 node_44
theorem node_41 : Covered ((12437 / 16000 : ℚ),(1247 / 1600 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (12437 / 16000 : ℚ) (1247 / 1600 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (24907 / 32000 : ℚ) node_42 node_45
theorem node_40 : Covered ((12437 / 16000 : ℚ),(1247 / 1600 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_39 : Covered ((12437 / 16000 : ℚ),(1247 / 1600 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12437 / 16000 : ℚ) (1247 / 1600 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_40 node_41
theorem node_38 : Covered ((24841 / 32000 : ℚ),(12437 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_37 : Covered ((3101 / 4000 : ℚ),(24841 / 32000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_36 : Covered ((3101 / 4000 : ℚ),(12437 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (3101 / 4000 : ℚ) (12437 / 16000 : ℚ) (31 / 752 : ℚ) (2 / 47 : ℚ) (24841 / 32000 : ℚ) node_37 node_38
theorem node_35 : Covered ((3101 / 4000 : ℚ),(12437 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_34 : Covered ((3101 / 4000 : ℚ),(12437 / 16000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3101 / 4000 : ℚ) (12437 / 16000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_35 node_36
theorem node_33 : Covered ((3101 / 4000 : ℚ),(1247 / 1600 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (3101 / 4000 : ℚ) (1247 / 1600 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (12437 / 16000 : ℚ) node_34 node_39
theorem node_32 : Covered ((3101 / 4000 : ℚ),(1247 / 1600 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_31 : Covered ((3101 / 4000 : ℚ),(1247 / 1600 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3101 / 4000 : ℚ) (1247 / 1600 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_32 node_33
theorem node_30 : Covered ((3101 / 4000 : ℚ),(1567 / 2000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (3101 / 4000 : ℚ) (1567 / 2000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (1247 / 1600 : ℚ) node_31 node_48
theorem node_29 : Covered ((3101 / 4000 : ℚ),(1567 / 2000 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_28 : Covered ((3101 / 4000 : ℚ),(1567 / 2000 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (3101 / 4000 : ℚ) (1567 / 2000 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_29 node_30
theorem node_27 : Covered ((12371 / 16000 : ℚ),(3101 / 4000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_26 : Covered ((12371 / 16000 : ℚ),(3101 / 4000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_25 : Covered ((12371 / 16000 : ℚ),(3101 / 4000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (12371 / 16000 : ℚ) (3101 / 4000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_26 node_27
theorem node_24 : Covered ((6169 / 8000 : ℚ),(12371 / 16000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_23 : Covered ((6169 / 8000 : ℚ),(12371 / 16000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_22 : Covered ((6169 / 8000 : ℚ),(12371 / 16000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6169 / 8000 : ℚ) (12371 / 16000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_23 node_24
theorem node_21 : Covered ((6169 / 8000 : ℚ),(3101 / 4000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (6169 / 8000 : ℚ) (3101 / 4000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (12371 / 16000 : ℚ) node_22 node_25
theorem node_20 : Covered ((6169 / 8000 : ℚ),(3101 / 4000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_19 : Covered ((6169 / 8000 : ℚ),(3101 / 4000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (6169 / 8000 : ℚ) (3101 / 4000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_20 node_21
theorem node_18 : Covered ((2461 / 3200 : ℚ),(6169 / 8000 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_17 : Covered ((2461 / 3200 : ℚ),(6169 / 8000 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_16 : Covered ((2461 / 3200 : ℚ),(6169 / 8000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (2461 / 3200 : ℚ) (6169 / 8000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_17 node_18
theorem node_15 : Covered ((767 / 1000 : ℚ),(2461 / 3200 : ℚ)) ((31 / 752 : ℚ),(2 / 47 : ℚ)) := by
 intro c j hc hj
 exact moment_sound (t := (0 / 1 : ℚ)) hc hj (by decide +kernel)
theorem node_14 : Covered ((767 / 1000 : ℚ),(2461 / 3200 : ℚ)) ((15 / 376 : ℚ),(31 / 752 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_13 : Covered ((767 / 1000 : ℚ),(2461 / 3200 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (767 / 1000 : ℚ) (2461 / 3200 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (31 / 752 : ℚ) node_14 node_15
theorem node_12 : Covered ((767 / 1000 : ℚ),(6169 / 8000 : ℚ)) ((15 / 376 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (767 / 1000 : ℚ) (6169 / 8000 : ℚ) (15 / 376 : ℚ) (2 / 47 : ℚ) (2461 / 3200 : ℚ) node_13 node_16
theorem node_11 : Covered ((767 / 1000 : ℚ),(6169 / 8000 : ℚ)) ((7 / 188 : ℚ),(15 / 376 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_10 : Covered ((767 / 1000 : ℚ),(6169 / 8000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (767 / 1000 : ℚ) (6169 / 8000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (15 / 376 : ℚ) node_11 node_12
theorem node_9 : Covered ((767 / 1000 : ℚ),(3101 / 4000 : ℚ)) ((7 / 188 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (767 / 1000 : ℚ) (3101 / 4000 : ℚ) (7 / 188 : ℚ) (2 / 47 : ℚ) (6169 / 8000 : ℚ) node_10 node_19
theorem node_8 : Covered ((767 / 1000 : ℚ),(3101 / 4000 : ℚ)) ((3 / 94 : ℚ),(7 / 188 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_7 : Covered ((767 / 1000 : ℚ),(3101 / 4000 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (767 / 1000 : ℚ) (3101 / 4000 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (7 / 188 : ℚ) node_8 node_9
theorem node_6 : Covered ((767 / 1000 : ℚ),(1567 / 2000 : ℚ)) ((3 / 94 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (767 / 1000 : ℚ) (1567 / 2000 : ℚ) (3 / 94 : ℚ) (2 / 47 : ℚ) (3101 / 4000 : ℚ) node_7 node_28
theorem node_5 : Covered ((767 / 1000 : ℚ),(1567 / 2000 : ℚ)) ((1 / 47 : ℚ),(3 / 94 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_4 : Covered ((767 / 1000 : ℚ),(1567 / 2000 : ℚ)) ((1 / 47 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (767 / 1000 : ℚ) (1567 / 2000 : ℚ) (1 / 47 : ℚ) (2 / 47 : ℚ) (3 / 94 : ℚ) node_5 node_6
theorem node_3 : Covered ((767 / 1000 : ℚ),(4 / 5 : ℚ)) ((1 / 47 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (767 / 1000 : ℚ) (4 / 5 : ℚ) (1 / 47 : ℚ) (2 / 47 : ℚ) (1567 / 2000 : ℚ) node_4 node_69
theorem node_2 : Covered ((767 / 1000 : ℚ),(4 / 5 : ℚ)) ((0 / 1 : ℚ),(1 / 47 : ℚ)) := by
 intro c j hc hj
 exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem node_1 : Covered ((767 / 1000 : ℚ),(4 / 5 : ℚ)) ((0 / 1 : ℚ),(2 / 47 : ℚ)) := by
 exact split_j (767 / 1000 : ℚ) (4 / 5 : ℚ) (0 / 1 : ℚ) (2 / 47 : ℚ) (1 / 47 : ℚ) node_2 node_3
theorem node_0 : Covered ((767 / 1000 : ℚ),(22 / 25 : ℚ)) ((0 / 1 : ℚ),(2 / 47 : ℚ)) := by
 exact split_c (767 / 1000 : ℚ) (22 / 25 : ℚ) (0 / 1 : ℚ) (2 / 47 : ℚ) (4 / 5 : ℚ) node_1 node_314
theorem middle : Covered (767/1000,22/25) (0,I) := node_0
end E10
