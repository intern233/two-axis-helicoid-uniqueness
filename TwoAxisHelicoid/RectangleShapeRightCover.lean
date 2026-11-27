import TwoAxisHelicoid.RectangleShapeRightGroup000
import TwoAxisHelicoid.RectangleShapeRightGroup001
import TwoAxisHelicoid.RectangleShapeRightGroup002
import TwoAxisHelicoid.RectangleShapeRightGroup003
namespace TwoAxisHelicoid
theorem rectangleShapeRightCover : CheckedRectangleShape false (1/8) (3/8) :=
  (.join (.join checkedRectangleShapeRightGroup000 checkedRectangleShapeRightGroup001) (.join checkedRectangleShapeRightGroup002 checkedRectangleShapeRightGroup003))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangleShapeRightCover
