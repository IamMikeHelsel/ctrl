namespace Fixture
 theorem indented_public : True := True.intro
@[simp] theorem attributed_public : True := True.intro
theorem plain_public : True := True.intro
end Fixture
#print axioms Fixture.indented_public
#print axioms Fixture.attributed_public
#print axioms Fixture.plain_public
